/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Constant
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Descent
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Gluing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite locally constant sheaves of sets are finite étale schemes

Let `T` be a scheme. We show:

* for a finite étale `π : P ⟶ T`, the presheaf of sections `U ↦ Hom_T(U, P)` on the small étale
  site of `T` is a sheaf with finite stalks, which is constant over the members of an étale
  cover of `T` (`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_uliftYoneda`);
* every sheaf of sets on the small étale site of `T` with finite stalks which is constant over
  the members of an étale cover of `T` is isomorphic to the sheaf of sections of a finite étale
  `T`-scheme (`AlgebraicGeometry.Scheme.exists_iso_uliftYoneda_of_isFiniteLocallyConstant`).

These are the two object-level halves of blueprint node
`lemma-weil-pbc-finite-locally-constant-etale-equivalence`, combined in
`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso'`; the finiteness and
local constancy conditions are those of
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheafOfTypes`
(which is defined in `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`, a downstream file).

## Proof

For the first statement, `P` becomes a trivial cover `∐_{S} U ⟶ U` over the members of an
étale cover (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), and the
sheaf of sections of a trivial cover is constant
(`AlgebraicGeometry.Scheme.Etale.isConstant_over_of_isUniversalSection`). Its stalk at a
geometric point is a quotient of the finite geometric fibre of `P`.

For the second statement, a constant sheaf with finite stalks over `U` is represented by a
trivial finite cover of `U`
(`AlgebraicGeometry.Scheme.Etale.exists_isUniversalSection_of_isConstant`).
Over an affine open `W` of `T`, finitely many affine opens of the members of the cover give a
surjective étale `p : X ⟶ W` from an affine scheme; the trivial covers glue to a finite étale
`X`-scheme representing the restriction of `E` to `X`
(`AlgebraicGeometry.Scheme.exists_isUniversalSection_of_forall_exists_opens`), which descends to
`W` (`AlgebraicGeometry.Scheme.IsUniversalSection.exists_isUniversalSection_of_isAffine`). The
representing schemes over the affine opens of `T` glue to a finite étale `T`-scheme representing
`E`, again by `AlgebraicGeometry.Scheme.exists_isUniversalSection_of_forall_exists_opens`.

## References

- Stacks Project, Tag 03RV (finite locally constant sheaves and finite étale morphisms)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}}

/-! ### Sheaves of sections of finite étale schemes -/

/-- The presheaf of sections of an étale `T`-scheme is a sheaf on the small étale site: the small
étale topology is subcanonical. -/
lemma isSheaf_uliftYoneda (P : T.Etale) :
    Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj P) :=
  (T.smallEtaleTopology.uliftYoneda.{u + 1}.obj P).property

/-- The stalks of the sheaf of sections of a finite étale `T`-scheme are finite: the stalk at a
geometric point `s` is a quotient of the geometric fibre of `P` at `s`, every germ of a
section `a : V ⟶ P` at a point `v` of `V` over `s` being the germ of the identity of `P` at
the point `a ∘ v`. -/
lemma isFiniteSheaf_uliftYoneda (P : T.Etale) [IsFinite P.hom] :
    IsFiniteSheaf (⟨_, isSheaf_uliftYoneda P⟩ : Sheaf T.smallEtaleTopology (Type (u + 1))) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    let Φ := pointSmallEtale s
    have : Finite (Φ.fiber.obj P) :=
      FiniteEtale.finite_fiber s (⟨P, ‹IsFinite P.hom›⟩ : T.FiniteEtale)
    change Finite (ToType (Φ.presheafFiber.obj (uliftYoneda.{u + 1}.obj P)))
    refine Finite.of_surjective
      (fun z : Φ.fiber.obj P ↦ Φ.toPresheafFiber P z (uliftYoneda.{u + 1}.obj P) ⟨𝟙 P⟩)
      fun p ↦ ?_
    obtain ⟨V, v, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
    refine ⟨Φ.fiber.map a.down v, ?_⟩
    have := GrothendieckTopology.Point.toPresheafFiber_w_apply (Φ := Φ) a.down v
      (uliftYoneda.{u + 1}.obj P) ⟨𝟙 P⟩
    exact this.symm.trans (congrArg _ (ULift.ext (Category.comp_id a.down : a.down ≫ 𝟙 P = _)))

/-- The sheaf of sections of a finite étale `T`-scheme is constant over the members of an étale
cover of `T`, over which `P` becomes a trivial cover. -/
lemma exists_cover_isConstant_over_uliftYoneda (P : T.Etale) [IsFinite P.hom] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (Sheaf.over (⟨_, isSheaf_uliftYoneda P⟩ : Sheaf T.smallEtaleTopology (Type (u + 1)))
        (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := by
  choose U g hg S hS fst hy hpb using fun t : T ↦
    FiniteEtale.exists_etale_isPullback_sigma (⟨P, ‹IsFinite P.hom›⟩ : T.FiniteEtale) t
  let 𝒰 : Cover.{u} etalePrecoverage T :=
    Cover.mkOfCovers T U g (fun t ↦ ⟨t, (hy t)⟩) (fun t ↦ hg t)
  refine ⟨𝒰, fun t ↦ ?_⟩
  let E : Sheaf T.smallEtaleTopology (Type (u + 1)) := ⟨_, isSheaf_uliftYoneda P⟩
  let Ut := 𝒰.etalePrecoverageToEtale t
  have : AlgebraicGeometry.Etale (g t) := hg t
  -- the universal section of `E` over the trivial cover of `U t`
  have h₀ := isUniversalSection_uliftYoneda.{u + 1} P
  have h₁ := h₀.baseChange (o := g t) (u' := g t) rfl (Category.comp_id _)
  let e : Etale.trivialCover Ut (S t) ≅ IsUniversalSection.baseChangeObj
      (u := 𝟙 T) (V := P) (v := P.hom) rfl (g t) (g t) :=
    MorphismProperty.Over.isoMk (hpb t).isoPullback (by
      change (hpb t).isoPullback.hom ≫ pullback.snd P.hom (g t) ≫ g t = _ ≫ g t
      rw [IsPullback.isoPullback_hom_snd_assoc]
      rfl)
  have h₂ := (h₁.of_iso e).of_eq (v' := Sigma.desc fun _ ↦ 𝟙 (U t))
    (IsPullback.isoPullback_hom_snd _)
  exact Etale.isConstant_over_of_isUniversalSection E Ut (S t) h₂

/-- **The sheaf of sections of a finite étale scheme is finite locally constant.**
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem isFiniteLocallyConstant_uliftYoneda (P : Scheme.{u}) (π : P ⟶ T) [IsFinite π]
    [AlgebraicGeometry.Etale π] :
    ∃ h : Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj (Etale.mk π)),
      (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
        (Sheaf.over (⟨_, h⟩ : Sheaf T.smallEtaleTopology (Type (u + 1)))
          (𝒰.etalePrecoverageToEtale i)).IsConstant
          (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧
      IsFiniteSheaf (⟨_, h⟩ : Sheaf T.smallEtaleTopology (Type (u + 1))) :=
  have : IsFinite (Etale.mk π).hom := ‹_›
  ⟨isSheaf_uliftYoneda _, exists_cover_isConstant_over_uliftYoneda _,
    isFiniteSheaf_uliftYoneda _⟩
/-! ### Finite locally constant sheaves are represented by finite étale schemes -/

section Representable

variable (E : Sheaf T.smallEtaleTopology (Type (u + 1))) (𝒰 : Cover.{u} etalePrecoverage T)
  (h𝒰 : ∀ i, (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
    (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
  (hfin : IsFiniteSheaf E)

include h𝒰 hfin in
/-- **Representability over an affine open.** Let `E` be a sheaf of sets on the small étale site
of `T` with finite stalks which is constant over the members of an étale cover `𝒰` of `T`. Then
over every affine open `W` of `T` the sheaf `E` is represented by a finite étale `W`-scheme:
finitely many affine opens `O_k` of members of `𝒰` cover `W`, over each of them `E` is
represented by a trivial finite cover, these glue to a finite étale scheme over `X = ∐ O_k`,
which descends along the surjective étale `X ⟶ W`.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem isRepresentableOver_of_isAffineOpen {W : T.Opens} (hW : IsAffineOpen W) :
    IsRepresentableOver E.obj (𝟙 T) W := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  -- for every point `y` of `W`, an affine open `O y` of a member of the cover lying over `W`
  -- whose image contains `y`
  have hy (y : W) : ∃ (i : 𝒰.I₀) (O : (𝒰.X i).Opens), IsAffineOpen O ∧
      (y : T) ∈ (𝒰.f i) '' O ∧ O ≤ (𝒰.f i) ⁻¹ᵁ W := by
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq y.1
    have hxW : x ∈ (𝒰.f i) ⁻¹ᵁ W := by
      change 𝒰.f i x ∈ W
      rw [hx]
      exact y.2
    obtain ⟨O, hO, hxO, hOW⟩ := exists_isAffineOpen_mem_and_subset hxW
    exact ⟨i, O, hO, ⟨x, hxO, hx⟩, hOW⟩
  choose i O hO hyO hOW using hy
  -- finitely many of them cover `W`
  have hopen (y : W) : IsOpen ((𝒰.f (i y)) '' (O y)) := (𝒰.f (i y)).isOpenMap _ (O y).2
  obtain ⟨t, ht⟩ := hW.isCompact.elim_finite_subcover (fun y : W ↦ (𝒰.f (i y)) '' (O y)) hopen
    (fun y hy ↦ Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩)
  let K := {y : W // y ∈ t}
  let Ok (k : K) : Scheme.{u} := (O k.1).toScheme
  have : ∀ k, IsAffine (Ok k) := fun k ↦ hO k.1
  have : IsAffine W.toScheme := hW
  have hrange (k : K) : Set.range ((O k.1).ι ≫ 𝒰.f (i k.1)) ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hOW k.1 z.2
  let lk (k : K) : Ok k ⟶ W := IsOpenImmersion.lift W.ι ((O k.1).ι ≫ 𝒰.f (i k.1)) (hrange k)
  have hlk (k : K) : lk k ≫ W.ι = (O k.1).ι ≫ 𝒰.f (i k.1) := IsOpenImmersion.lift_fac _ _ _
  have : ∀ k, AlgebraicGeometry.Etale (lk k) := fun k ↦ by
    have : AlgebraicGeometry.Etale (lk k ≫ W.ι) := by rw [hlk]; infer_instance
    exact AlgebraicGeometry.Etale.of_comp (lk k) W.ι
  let X : Scheme.{u} := ∐ Ok
  let p : X ⟶ W := Sigma.desc lk
  have : AlgebraicGeometry.Etale p := IsZariskiLocalAtSource.sigmaDesc fun k ↦ inferInstance
  have : AlgebraicGeometry.Surjective p := ⟨fun y ↦ by
    obtain ⟨k, hk, z, hz, hzy⟩ := Set.mem_iUnion₂.1 (ht y.2)
    refine ⟨Sigma.ι Ok ⟨k, hk⟩ ⟨z, hz⟩, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc_assoc, hlk]
    exact hzy⟩
  let s : W.toScheme ⟶ T := W.ι ≫ 𝟙 T
  -- over the summands of `X`, the sheaf `E` is represented by trivial finite covers
  have H (z : X) : ∃ Wz : X.Opens, z ∈ Wz ∧ IsRepresentableOver E.obj (p ≫ s) Wz := by
    obtain ⟨k, z', rfl⟩ := (sigmaOpenCover Ok).exists_eq z
    let ιk : Ok k ⟶ X := Sigma.ι Ok k
    refine ⟨ιk.opensRange, ⟨z', rfl⟩, ?_⟩
    let U := 𝒰.etalePrecoverageToEtale (i k.1)
    have := h𝒰 (i k.1)
    obtain ⟨S', _, ξ, hξ⟩ := Etale.exists_isUniversalSection_of_isConstant E U hfin z'.1
    let o : ιk.opensRange.toScheme ⟶ U.left := ιk.isoOpensRange.inv ≫ (O k.1).ι
    have ho : o ≫ U.hom = ιk.opensRange.ι ≫ p ≫ s := by
      rw [← cancel_epi ιk.isoOpensRange.hom]
      change ιk.isoOpensRange.hom ≫ ιk.isoOpensRange.inv ≫ (O k.1).ι ≫ 𝒰.f (i k.1) =
        ιk.isoOpensRange.hom ≫ ιk.opensRange.ι ≫ p ≫ W.ι ≫ 𝟙 T
      rw [Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, Sigma.ι_comp_desc_assoc,
        Category.comp_id, hlk]
    exact ⟨_, pullback.snd _ o,
      MorphismProperty.pullback_snd _ _ (IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance),
      inferInstance, _, hξ.baseChange rfl ho⟩
  obtain ⟨PX, πX, _, _, ξX, hX⟩ := exists_isUniversalSection_of_forall_exists_opens E.property
    (p ≫ s) H
  obtain ⟨N, n, _, _, ξ₀, h₀⟩ :=
    IsUniversalSection.exists_isUniversalSection_of_isAffine (s := s) hX E.property
  exact ⟨N, n, ‹_›, ‹_›, ξ₀, h₀⟩

end Representable

/-- **Finite locally constant sheaves of sets are represented by finite étale schemes.** Every
sheaf of sets on the small étale site of `T` with finite stalks which is constant over the
members of an étale cover of `T` is isomorphic to the sheaf of sections of a finite étale
`T`-scheme. (blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem exists_iso_uliftYoneda_of_isFiniteLocallyConstant
    (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hE : (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ IsFiniteSheaf E) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : AlgebraicGeometry.Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hE
  obtain ⟨P, π, _, _, ξ, h⟩ := exists_isUniversalSection_of_forall_exists_opens E.property (𝟙 T)
    fun x ↦ by
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact ⟨W, hxW, isRepresentableOver_of_isAffineOpen E 𝒰 h𝒰 hfin hW⟩
  have h' : IsUniversalSection E.obj (𝟙 T) (Etale.mk (π ≫ 𝟙 T)) (Etale.mk (π ≫ 𝟙 T)).hom ξ :=
    h.of_eq (Category.comp_id π).symm
  exact ⟨P, π, ‹_›, ‹_›, ⟨h'.isoUliftYoneda ≪≫ uliftYoneda.{u + 1}.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 P ≫ π = π ≫ 𝟙 T
      rw [Category.id_comp, Category.comp_id]))⟩⟩

/-- **Finite locally constant sheaves of sets and finite étale schemes.** For a scheme `T`:

* for every finite étale `π : P ⟶ T`, the presheaf of sections `U ↦ Hom_T(U, P)` on the small
  étale site is a sheaf, constant over the members of an étale cover of `T`, with finite stalks;
* every sheaf of sets with finite stalks which is constant over the members of an étale cover
  of `T` is isomorphic to the sheaf of sections of a finite étale `T`-scheme.

This is `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso` with
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheafOfTypes` unfolded.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem isFiniteLocallyConstant_yoneda_and_exists_iso' (T : Scheme.{u}) :
    (∀ (P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [AlgebraicGeometry.Etale π],
      ∃ h : Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj (Etale.mk π)),
        (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
          (Sheaf.over (⟨_, h⟩ : Sheaf T.smallEtaleTopology (Type (u + 1)))
            (𝒰.etalePrecoverageToEtale i)).IsConstant
            (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧
        IsFiniteSheaf (⟨_, h⟩ : Sheaf T.smallEtaleTopology (Type (u + 1)))) ∧
    ∀ E : Sheaf T.smallEtaleTopology (Type (u + 1)),
      ((∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
        (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
          (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ IsFiniteSheaf E) →
      ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : AlgebraicGeometry.Etale π),
        Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) :=
  ⟨fun P π _ _ ↦ isFiniteLocallyConstant_uliftYoneda P π,
    fun E hE ↦ exists_iso_uliftYoneda_of_isFiniteLocallyConstant E hE⟩

end AlgebraicGeometry.Scheme
