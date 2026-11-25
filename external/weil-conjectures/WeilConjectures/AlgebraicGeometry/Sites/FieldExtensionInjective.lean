/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Injectivity of the pullback to an extension of an algebraically closed field

Let `k` be an algebraically closed field, `X` a quasi-compact quasi-separated `k`-scheme and
`k'` a field extension of `k`. Then the pullback map `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is injective
for every abelian étale sheaf `F` on `X`.

The base change `X_{k'}` is the limit of the `X_A = X ×_k Spec A` over the finitely generated
`k`-subalgebras `A ⊆ k'`, so by continuity of étale cohomology a class dying on `X_{k'}` dies on
some `X_A`; and `X_A ⟶ X` has a section, given by a `k`-point of `Spec A` (Nullstellensatz).

## Main statements

- `AlgebraicGeometry.injective_cohomologyMap_pullback_fst_of_isAlgClosed`: the injectivity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open CommRingCat

/-- **Injectivity of the pullback to a field extension.** Let `k` be an algebraically closed
field, `X` a quasi-compact quasi-separated `k`-scheme, `k'` a field extension of `k` and `F` an
abelian étale sheaf on `X`. Then the pullback `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` along the projection
`X_{k'} ⟶ X` is injective. -/
theorem injective_cohomologyMap_pullback_fst_of_isAlgClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X] (k' : Type u) [Field k'] [Algebra k k']
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Injective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q) := by
  classical
  let I := {A : Subalgebra k k' // A.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder I := ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    show A.1 ≤ A.1 ⊔ B.1 from le_sup_left, show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (fgSubalgebraDiagramOf k k').op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (fgSubalgebraCoconeOf k k').op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (isColimitFGSubalgebraCocone k k').op
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let ρ : CommRingCat.of (⊥ : Subalgebra k k') ≅ CommRingCat.of k :=
    (Algebra.botEquiv k k').toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := f ≫ Spec.map ρ.hom
  have hring : (CommRingCat.ofHom (⊥ : Subalgebra k k').val.toRingHom :
      CommRingCat.of (⊥ : Subalgebra k k') ⟶ .of k') =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap k k') := by
    ext x
    obtain ⟨r, rfl⟩ := (Algebra.botEquiv k k').symm.surjective x
    simp [ρ]
  have hρK : c.π.app i₀ = Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ Spec.map ρ.hom := by
    rw [← Spec.map_comp, ← hring]
    rfl
  have H1 : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (pullback.snd _ _) p (c.π.app i₀) := by
    rw [hρK]
    exact (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map ρ.hom)) (by simp) (by simp) (by simp [p]) (by simp)
  let eX := (IsPullback.of_hasPullback p (c.π.app i₀)).isoIsPullback _ _ H1
  have heX : eX.hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) =
      pullback.fst p (c.π.app i₀) := IsPullback.isoIsPullback_hom_fst _ _ _ H1
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  -- the system of the `X_A` over `X`
  let D'' : Over i₀ ⥤ Over X :=
    { obj j := Over.mk (pullback.fst p (D.map j.hom))
      map g := Over.homMk (D'.map g) (baseChangeDiagram_map_fst D p g)
      map_id j := by ext1; exact D'.map_id j
      map_comp g h := by ext1; exact D'.map_comp g h }
  let c'' : Cone D'' :=
    { pt := Over.mk (pullback.fst p (c.π.app i₀))
      π := { app j := Over.homMk (c'.π.app j) (baseChangeCone_π_app_fst D c p j)
             naturality j j' g := by ext1; exact c'.π.naturality g } }
  have hc'' : IsLimit ((Over.forget X).mapCone c'') := hc'
  have : IsAffine (D.obj i₀) := inferInstanceAs (IsAffine (Spec _))
  have : QuasiCompact p := (quasiCompact_iff_compactSpace p).mpr inferInstance
  have : QuasiSeparated p := (quasiSeparated_iff_quasiSeparatedSpace p).mpr inferInstance
  have (j : Over i₀) : CompactSpace (D''.obj j).left := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (D.map j.hom))
  have (j : Over i₀) : QuasiSeparatedSpace (D''.obj j).left := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    exact (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (D.map j.hom))).mp inferInstance
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := hD
  have (j j' : Over i₀) (g : j ⟶ j') : IsAffineHom (D''.map g).left :=
    inferInstanceAs (IsAffineHom (D'.map g))
  have hcont := Etale.cohomologyMap_isColimit_of_isLimit F D'' c'' hc'' q
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- the class dies on the limit `X ×_{Spec ⊥} lim Spec A`
  have h₁ : Etale.cohomologyMap (pullback.fst p (c.π.app i₀)) F q x = 0 := by
    rw [← Etale.cohomologyMap_cohomologyMap_eq_zero_iff' eX.hom _ _ heX, hx, map_zero]
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  let y := Etale.cohomologyMap (pullback.fst p (D.map j₀.hom)) F q x
  have hy : Etale.cohomologyMap (c''.π.app j₀).left _ q y = 0 := by
    exact (Etale.cohomologyMap_cohomologyMap_eq_zero_iff' ((baseChangeCone D c p).π.app j₀) _ _
      (baseChangeCone_π_app_fst D c p j₀) F x).2 h₁
  -- hence on some `X_A`
  obtain ⟨j, g, hg⟩ := hcont.2 j₀ y hy
  have h₂ : Etale.cohomologyMap (pullback.fst p (D.map j.hom)) F q x = 0 := by
    exact (Etale.cohomologyMap_cohomologyMap_eq_zero_iff' (D'.map g)
      (pullback.fst p (D.map j₀.hom)) _ (baseChangeDiagram_map_fst D p g) F x).1 hg
  -- a `k`-point of `Spec A` gives a section of `X_A ⟶ X`
  let A : Subalgebra k k' := j.left.unop.1
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType _).mp j.left.unop.2
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  let φ : A →ₐ[k] (⊥ : Subalgebra k k') :=
    ((Algebra.botEquiv k k').symm.toAlgHom.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ k m)
  let t : D.obj i₀ ⟶ D.obj j.left := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have ht : t ≫ D.map j.hom = 𝟙 _ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    change Spec.map (_ ≫ _) = 𝟙 (Spec (CommRingCat.of (⊥ : Subalgebra k k')))
    rw [← Spec.map_id]
    congr 1
    ext b
    obtain ⟨r, rfl⟩ := (Algebra.botEquiv k k').symm.surjective b
    exact congrArg Subtype.val (φ.commutes r)
  let s : X ⟶ pullback p (D.map j.hom) := pullback.lift (𝟙 X) (p ≫ t) (by simp [ht])
  exact Etale.injective_cohomologyMap_of_comp_eq_id _ s (pullback.lift_fst _ _ _) F q
    (h₂.trans (map_zero _).symm)

end AlgebraicGeometry
