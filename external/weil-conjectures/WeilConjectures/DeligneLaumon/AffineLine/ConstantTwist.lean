/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.FourierTateTwist.Transform

/-!
# Constant twists of lisse sheaves on a dense open of the affine line

A constant Weil twist `M ⊗ 𝓑_b` by a unit `b ∈ ℚ̄_ℓˣ` keeps the underlying `ℓ`-adic sheaf of
`M` and multiplies its Weil structure by `b`. It is an autoequivalence of the category of Weil
sheaves, so it preserves irreducibility; it does not see the geometric constituents, so it
preserves nonexceptionality; and it commutes with direct images and with the Fourier transform,
so a Fourier partner of `M` twisted by `b` is a Fourier partner of `M ⊗ 𝓑_b`.

Since `|ι b|` can be chosen to be any real power of `q` attained by an eigenvalue of Frobenius,
this reduces the purity of Fourier partners
(`AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner`) to sheaves pure of
weight `0`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.constantTwistEquivalence`: the constant twist as an
  autoequivalence of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.constantTwist`: twists of irreducible lisse
  sheaves are irreducible.
- `AlgebraicGeometry.WeilSheaf.directImageConstantTwistIso`: `j_*(F ⊗ 𝓑_b) ≅ (j_*F) ⊗ 𝓑_b`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.constantTwist` and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierPartner.constantTwist`.
- `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner_of_weight_zero`: the
  reduction of the purity of Fourier partners to weight `0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Equivalence

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant twist of Weil sheaves is an autoequivalence, with inverse the twist by the
inverse automorphism. Its functor is the restriction of the constant twist
`AlgebraicGeometry.ProEtaleWeilSheaf.constantTwist` of pro-étale Weil sheaves, which does not
change the underlying sheaf. -/
noncomputable def constantTwistEquivalence (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X ≌ WeilSheaf k₀ l X :=
  let E := IsoAlgebra.twistEquivalence (ProEtaleWeilSheaf.frobeniusPullbackSmulIso k₀ l X b)
  let P := WeilSheaf.objectProperty k₀ l X
  { functor := P.liftFullSubcategory P (ProEtaleWeilSheaf.constantTwist k₀ l X b) fun _ hF ↦ hF
    inverse := P.liftFullSubcategory P E.inverse fun _ hF ↦ hF
    unitIso := NatIso.ofComponents (fun F ↦ P.isoMk (E.unitIso.app F.obj)) fun _ ↦
      ObjectProperty.hom_ext _ (IsoAlgebra.hom_ext
        ((Category.comp_id _).trans (Category.id_comp _).symm))
    counitIso := NatIso.ofComponents (fun F ↦ P.isoMk (E.counitIso.app F.obj)) fun _ ↦
      ObjectProperty.hom_ext _ (IsoAlgebra.hom_ext
        ((Category.comp_id _).trans (Category.id_comp _).symm))
    functor_unitIso_comp _ := ObjectProperty.hom_ext _ (IsoAlgebra.hom_ext (Category.id_comp _)) }

/-- The constant twist `F.constantTwist b` is the image of `F` under the constant twist
autoequivalence. -/
noncomputable def constantTwistIsoConstantTwistEquivalenceObj (F : WeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) : F.constantTwist b ≅ (constantTwistEquivalence b).functor.obj F :=
  ObjectProperty.isoMk _ (F.constantTwistObjIso b)

/-- Being irreducible lisse is invariant under isomorphism. -/
theorem IsIrreducibleLisse.of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (h : F.IsIrreducibleLisse) : G.IsIrreducibleLisse := by
  refine ⟨h.1.of_iso e, fun hG ↦ h.2.1 (hG.of_iso e), fun H i hi hH ↦ ?_⟩
  obtain h' | h' := h.2.2 H (i ≫ e.inv) inferInstance hH
  · exact Or.inl h'
  · have : IsIso i := IsIso.of_isIso_comp_right i e.inv
    exact Or.inr this

-- The instances `PreservesZeroMorphisms` of the equivalence take longer to find with the full
-- import context (`WeilSheaf.Localization` upstream).
/-- An autoequivalence `E` of Weil sheaves whose inverse preserves lisse sheaves maps irreducible
lisse sheaves to irreducible lisse sheaves. -/
theorem IsIrreducibleLisse.map_equivalence (E : WeilSheaf k₀ l X ≌ WeilSheaf k₀ l X)
    (hE : ∀ G, (E.inverse.obj G).IsLisse ↔ G.IsLisse) {F : WeilSheaf k₀ l X}
    (h : F.IsIrreducibleLisse) : (E.functor.obj F).IsIrreducibleLisse := by
  refine ⟨(hE _).1 (h.1.of_iso (E.unitIso.app F)), fun hF ↦ h.2.1
    ((E.inverse.map_isZero hF).of_iso (E.unitIso.app F)), fun G i hi hG ↦ ?_⟩
  have : Mono (E.inverse.map i) := E.inverse.map_mono i
  have : Mono (E.inverse.map i ≫ E.unitInv.app F) := mono_comp _ _
  obtain h' | h' := h.2.2 (E.inverse.obj G) (E.inverse.map i ≫ E.unitInv.app F) this
    ((hE G).2 hG)
  · exact Or.inl ((E.functor.map_isZero h').of_iso (E.counitIso.app G).symm)
  · have : IsIso (E.inverse.map i) := IsIso.of_isIso_comp_right _ (E.unitInv.app F)
    exact Or.inr (E.fullyFaithfulInverse.isIso_of_isIso_map i)

/-- The constant twist of an irreducible lisse Weil sheaf is irreducible lisse: the twist is
an autoequivalence of Weil sheaves which does not change underlying sheaves. -/
theorem IsIrreducibleLisse.constantTwist {F : WeilSheaf k₀ l X} (h : F.IsIrreducibleLisse)
    (b : (PadicAlgCl l)ˣ) : (F.constantTwist b).IsIrreducibleLisse :=
  (h.map_equivalence (constantTwistEquivalence b) fun _ ↦ Iff.rfl).of_iso
    (F.constantTwistIsoConstantTwistEquivalenceObj b).symm

end Equivalence

section DirectImage

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The direct image along a quasi-compact open immersion commutes with constant twists:
`j_*(F ⊗ 𝓑_b) ≅ (j_*F) ⊗ 𝓑_b`. -/
noncomputable def directImageConstantTwistIso (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) (b : (PadicAlgCl l)ˣ) :
    (directImage j).obj (F.constantTwist b) ≅ ((directImage j).obj F).constantTwist b :=
  ObjectProperty.isoMk _ ((ProEtaleWeilSheaf.lowerStar k₀ l j).mapIso (F.constantTwistObjIso b) ≪≫
    (ProEtaleWeilSheaf.constantTwistCompLowerStarIso k₀ l j b).app F.obj ≪≫
    (((directImage j).obj F).constantTwistObjIso b).symm)

/-- A shifted Weil sheaf twisted by `b` has as underlying object the constant twist by `b` of
the underlying object of the shifted sheaf, in the derived category of pro-étale Weil
sheaves. -/
noncomputable def shiftToComplexConstantTwistObjIso (G : WeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) (n : ℤ) :
    ((toComplex.obj (G.constantTwist b))⟦n⟧).obj ≅
      (ProEtaleWeilSheaf.constantTwist k₀ l X b).mapDerivedCategory.obj
        ((toComplex.obj G)⟦n⟧).obj :=
  let P := WeilComplex.objectProperty k₀ l X
  let T := (ProEtaleWeilSheaf.constantTwist k₀ l X b).mapDerivedCategory
  (P.ι.commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (G.constantTwistObjIso b) ≪≫
        ((ProEtaleWeilSheaf.constantTwist k₀ l X b).mapDerivedCategorySingleFunctor 0).symm.app
          G.obj) ≪≫
    ((T.commShiftIso n).app _).symm ≪≫
    T.mapIso ((P.ι.commShiftIso n).app (toComplex.obj G)).symm

end DirectImage

namespace LisseOnDenseOpen

/-- The constant twist `M ⊗ 𝓑_b` of the lisse sheaf of the datum, on the same dense open. -/
noncomputable def constantTwist (D : LisseOnDenseOpen k₀ l) (b : (PadicAlgCl l)ˣ) :
    LisseOnDenseOpen k₀ l :=
  { D with sheaf := D.sheaf.constantTwist b, lisse := D.lisse.constantTwist }

variable (D : LisseOnDenseOpen k₀ l) (b : (PadicAlgCl l)ˣ)

@[simp]
lemma constantTwist_sheaf : (D.constantTwist b).sheaf = D.sheaf.constantTwist b :=
  rfl

/-- The underlying object of the middle extension of the twisted datum is the constant twist
of that of the middle extension of the datum. -/
noncomputable def middleExtensionConstantTwistObjIso :
    (D.constantTwist b).middleExtension.obj ≅
      (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.obj
        D.middleExtension.obj :=
  (WeilComplex.objectProperty k₀ l (affineLine k₀)).ι.mapIso
      ((shiftFunctor _ (1 : ℤ)).mapIso
        (toComplex.mapIso (directImageConstantTwistIso D.j D.sheaf b))) ≪≫
    shiftToComplexConstantTwistObjIso D.directImage b 1

/-- **Fourier partners and constant twists.** If `D'` is a Fourier partner of `D`, then the
constant twist of `D'` by `b` is a Fourier partner of that of `D`: the middle extension, the
shift and the Fourier transform commute with constant twists. -/
theorem IsFourierPartner.constantTwist {ψ : AddChar k₀ (PadicAlgCl l)}
    {D D' : LisseOnDenseOpen k₀ l}
    (h : D.IsFourierPartner ψ D') (b : (PadicAlgCl l)ˣ) :
    (D.constantTwist b).IsFourierPartner ψ (D'.constantTwist b) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := nonempty_iso_fourierTransform_of_iso_constantTwist ψ b
    (D.middleExtensionConstantTwistObjIso b)
  let P := WeilComplex.objectProperty k₀ l (affineLine k₀)
  exact ⟨P.fullyFaithfulι.preimageIso (e' ≪≫
    (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.mapIso
      (P.ι.mapIso e) ≪≫ (D'.middleExtensionConstantTwistObjIso b).symm)⟩

/-- A constant twist does not change nonexceptionality, which only depends on the underlying
sheaf. -/
@[simp]
theorem isNonexceptional_constantTwist {ψ : AddChar k₀ (PadicAlgCl l)} :
    (D.sheaf.constantTwist b).IsNonexceptional ψ D.j ↔ D.sheaf.IsNonexceptional ψ D.j :=
  Iff.rfl

end LisseOnDenseOpen

end WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

open WeilSheaf in
/-- **Reduction of the purity of Fourier partners to weight `0`.** Suppose that the Fourier
partner of every irreducible nonexceptional lisse sheaf punctually `ι`-pure of weight `0` is
punctually `ι`-pure of some weight. Then the same holds for sheaves pure of any weight `w`: for
`M` nonzero and pure of weight `w` there is a unit `b` with `|ι b| = q^{-w/2}`, the twist
`M ⊗ 𝓑_b` is irreducible, nonexceptional and pure of weight `0`, with Fourier partner
`M' ⊗ 𝓑_b`, and `M' = (M' ⊗ 𝓑_b) ⊗ 𝓑_{b⁻¹}` is pure if `M' ⊗ 𝓑_b` is. -/
theorem exists_isPunctuallyPureOfWeight_of_isFourierPartner_of_weight_zero
    {ψ : AddChar k₀ (PadicAlgCl l)} {ι : PadicAlgCl l →+* ℂ}
    (h0 : ∀ D D' : LisseOnDenseOpen k₀ l, D.sheaf.IsIrreducibleLisse →
      D.sheaf.IsNonexceptional ψ D.j → D.sheaf.IsPunctuallyPureOfWeight ι 0 →
        D.IsFourierPartner ψ D' → ∃ v : ℝ, D'.sheaf.IsPunctuallyPureOfWeight ι v)
    (D D' : LisseOnDenseOpen k₀ l) (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D') :
    ∃ v : ℝ, D'.sheaf.IsPunctuallyPureOfWeight ι v := by
  have : LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over D.j (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (D'.U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over D'.j (Spec (CommRingCat.of k₀))]
    infer_instance
  obtain ⟨b, hb⟩ := D.sheaf.exists_norm_eq_of_isPunctuallyPureOfWeight ι hD.2.1 hw
  obtain ⟨v, hv⟩ := h0 (D.constantTwist b) (D'.constantTwist b) (hD.constantTwist b) hne
    (hw.constantTwist_zero hb) (hFT.constantTwist b)
  exact ⟨_, ((hv.constantTwist (b := b⁻¹) rfl).of_mono
    (D'.sheaf.constantTwistInvIso b).inv)⟩

end AlgebraicGeometry
