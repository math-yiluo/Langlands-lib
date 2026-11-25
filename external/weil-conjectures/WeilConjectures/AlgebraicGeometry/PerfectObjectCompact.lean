/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.DerivedTensorUnitCompact
import WeilConjectures.AlgebraicGeometry.PerfectTensorHomDuality

/-! # Compactness of perfect complexes

Source: Stacks Project, Proposition perfect-proposition-compact-is-perfect (Tag 09M1)
(blueprint: lem-pc-perfect-object-compact).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem compact_of_homEquiv
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    (R : C ⥤ C) [R.Additive] [PreservesColimitsOfSize.{u, u} R]
    (U P : C) (hU : IsCompactObject U)
    (e : ∀ M : C, (P ⟶ M) ≃+ (U ⟶ R.obj M))
    (he : ∀ {M N : C} (f : P ⟶ M) (g : M ⟶ N),
      e N (f ≫ g) = e M f ≫ R.map g) : IsCompactObject P := by
  classical
  intro I E
  let a := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp P (Sigma.ι E i))
  let b := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp U (Sigma.ι (fun i ↦ R.obj (E i)) i))
  let d := DirectSum.map (fun i ↦ (e (E i)).toAddMonoidHom)
  let t : (U ⟶ ∐ (fun i ↦ R.obj (E i))) ≃+ (U ⟶ R.obj (∐ E)) :=
    { (Iso.homCongr (Iso.refl U) (asIso (sigmaComparison R E))) with
      map_add' := by intros; simp }
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (E i)).injective),
      (DirectSum.map_surjective _).2 (fun i ↦ (e (E i)).surjective)⟩
  have hb : Function.Bijective b := hU I (fun i ↦ R.obj (E i))
  have hcomm : (e (∐ E)).toAddMonoidHom.comp a =
      t.toAddMonoidHom.comp (b.comp d) := by
    apply DirectSum.addHom_ext
    intro i f
    dsimp [a, b, d]
    simp only [DirectSum.toAddMonoid_of, DirectSum.map_of]
    simpa [t, Iso.homCongr, Preadditive.rightComp, Category.assoc] using
      he f (Sigma.ι E i)
  have hbij : Function.Bijective ((e (∐ E)).toAddMonoidHom.comp a) := by
    rw [hcomm]
    exact t.bijective.comp (hb.comp hd)
  exact Function.Bijective.of_comp_left hbij (e (∐ E)).injective

/-- Every perfect object of the quasi-coherent derived category of a quasi-compact,
quasi-separated scheme is compact.
Source: Stacks Project, Proposition perfect-proposition-compact-is-perfect (Tag 09M1)
(blueprint: lem-pc-perfect-object-compact).
Proof: (1) use `lem-pc-perfect-tensor-hom-duality` with the perfect dual of `P` to
identify `Hom(P, M)` naturally with `Hom(𝒪_X, P⁻¹ ⊗ᴸ M)`; (2) use
`lem-pc-kflat-resolution`, `lem-pc-derived-qcoh-direct-sums`,
`lem-pc-derived-ambient-direct-sums`, and `def-pc-tensor-complex-sheaves` to show
that tensoring by this dual commutes with set-indexed direct sums; (3) apply
`lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-derived-direct-image-preserves-direct-sums`, and
`lem-pc-affine-qcoh-derived-equivalence` to the structure morphism
`X ⟶ Spec(ℤ)`, so `Hom(𝒪_X, -)` commutes with direct sums, and conclude by
naturality. The empty family is included.
-/
theorem perfectObjectCompact (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.1 → IsCompactObject P := by
  let : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  intro P hP
  obtain ⟨U, ⟨eU⟩, hU⟩ := exists_compact_derivedTensorUnit X
  obtain ⟨D, _, _, ⟨adj⟩, ⟨adj'⟩, hclosed, _⟩ := perfect_tensor_hom_duality X P hP
  let Q := schemeDerivedQCohProperty X
  let F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory X :=
    Q.lift (Q.ι ⋙ MonoidalCategory.tensorLeft P.obj) (fun M ↦ (hclosed M).1)
  let G : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory X :=
    Q.lift (Q.ι ⋙ MonoidalCategory.tensorLeft D.obj) (fun M ↦ (hclosed M).2)
  let a : F ⊣ G := adj.restrictFullyFaithful Q.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  let a' : G ⊣ F := adj'.restrictFullyFaithful Q.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  let : G.IsLeftAdjoint := a'.isLeftAdjoint
  let : G.IsRightAdjoint := a.isRightAdjoint
  have : PreservesColimitsOfSize.{u, u} G := a'.leftAdjoint_preservesColimits
  have : HasFiniteCoproducts (schemeDerivedQCohCategory X) :=
    hasFiniteCoproducts_of_hasCoproducts _
  have : HasBinaryBiproducts (schemeDerivedQCohCategory X) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts G
  have : G.Additive := Functor.additive_of_preservesBinaryBiproducts G
  have : F.Additive := a.left_adjoint_additive
  let eP : F.obj U ≅ P := Q.isoMk
    ((MonoidalCategory.tensorLeft P.obj).mapIso eU ≪≫
      MonoidalCategory.rightUnitor P.obj)
  let e : ∀ M : schemeDerivedQCohCategory X, (P ⟶ M) ≃+ (U ⟶ G.obj M) :=
    fun M ↦ (show (P ⟶ M) ≃+ (F.obj U ⟶ M) from
      { Iso.homCongr eP.symm (Iso.refl M) with
        map_add' := by intros; simp }).trans (a.homAddEquiv U M)
  apply compact_of_homEquiv G U P hU e
  intro M N f g
  simpa [e, Iso.homCongr, Category.assoc] using
    a.homEquiv_naturality_right (eP.hom ≫ f) g

end AlgebraicGeometry
