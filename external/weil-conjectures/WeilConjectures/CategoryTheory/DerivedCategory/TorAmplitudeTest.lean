/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Testing Tor amplitude on a family of short exact sequences

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions. Suppose that flatness in `C` can be tested on a family of short exact sequences
`S_i : X₁ ⟶ X₂ ⟶ X₃`: an object `F` is flat as soon as every `F ◁ S_i.f` is a monomorphism (for
modules over a ring, the sequences `0 ⟶ I ⟶ R ⟶ R/I ⟶ 0` for the ideals `I`). Then an object
`K` of `D(C)` concentrated in `[a, b]` has Tor amplitude in `[a, b]` as soon as every
`K ⊗ᴸ S_i.X₃[0]` lies in degrees `≥ a` (`DerivedCategory.torAmplitudeIn_of_forall_isGE`).

This is the form of the residue-field test (`theorem-f-shriek-finite-coefficients--1`) used for the
direct image (`proposition-six-operations-dctf--2`): only finitely many test objects, all of them
constant, need to be controlled.

## Main results

- `CategoryTheory.ObjectProperty.mono_opcycles_whiskerLeft_of_exactAt`: the Tor criterion for a
  single short exact sequence.
- `DerivedCategory.torAmplitudeIn_of_forall_isGE`: the Tor amplitude test.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]

/-- **Tor criterion for one short exact sequence.** Let `P` be a cochain complex whose terms
`P^{a-1}` and `P^a` are flat, and let `S : X₁ ⟶ X₂ ⟶ X₃` be a short exact sequence such that
`P ⊗ X₃` is exact in degree `a - 1`. Then tensoring the cokernel `P^a / d(P^{a-1})` with
`S.f` gives a monomorphism.

The obstruction to injectivity is a cycle of `P ⊗ X₃` in degree `a - 1`, which is a boundary by
hypothesis. This is the diagram chase of
`CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, which applies it to every short exact
sequence. -/
lemma mono_opcycles_whiskerLeft_of_exactAt (P : CochainComplex C ℤ) (a : ℤ)
    (h₁ : flat (P.X (a - 1))) (h₂ : flat (P.X a)) (S : ShortComplex C) (hS : S.ShortExact)
    (hP : (((tensorRight S.X₃).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    Mono (P.opcycles a ◁ S.f) := by
  have := h₁.tensorLeft.preservesFiniteLimits
  have := h₂.tensorLeft.preservesFiniteLimits
  have := hS.mono_f
  have := hS.epi_g
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : C) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  -- the cokernel sequence `P^{a-1} ⟶ P^a ⟶ C ⟶ 0`, tensored with any object, stays exact
  have hcok (F : C) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : C) : Epi (p ▷ F) := (tensorRight F).map_epi p
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `P^a ⊗ S.X₁`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  -- its image in `P^a ⊗ S.X₂` dies in `C ⊗ S.X₂`, so it comes from `P^{a-1} ⊗ S.X₂`
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  -- the image of `z` in `P^{a-1} ⊗ S.X₃` is a cycle, hence a boundary
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 hP
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  have : Epi (P.X (a - 1 - 1) ◁ S.g) := (tensorLeft _).map_epi S.g
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  -- correcting `z` by a boundary, it comes from `P^{a-1} ⊗ S.X₁`
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

end CategoryTheory.ObjectProperty

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- **Testing Tor amplitude on a family of short exact sequences.** Let `S_i` be a family of
short exact sequences of `C` which detects flatness: an object `F` is flat as soon as every
`F ◁ S_i.f` is a monomorphism. Let `K` be an object of `D(C)` concentrated in degrees `[a, b]`
such that every `K ⊗ᴸ S_i.X₃[0]` lies in degrees `≥ a`. Then `K` has Tor amplitude in `[a, b]`.

Represent `K` by a complex `P` of flat objects vanishing above `b`. Its truncation `τ^{≥ a} P`
still represents `K`, and its term in degree `a`, the cokernel of `P^{a-1} ⟶ P^a`, is flat:
tensoring it with `S_i.f` is a monomorphism by
`CategoryTheory.ObjectProperty.mono_opcycles_whiskerLeft_of_exactAt`, as
`H^{a-1}(P ⊗ S_i.X₃) = H^{a-1}(K ⊗ᴸ S_i.X₃[0]) = 0`. So `K` has a flat model in degrees
`[a, b]`. -/
lemma torAmplitudeIn_of_forall_isGE {a b : ℤ} {K : DerivedCategory C} [K.IsGE a] [K.IsLE b]
    {ι : Type*} (S : ι → ShortComplex C) (hS : ∀ i, (S i).ShortExact)
    (hflat : ∀ F : C, (∀ i, Mono (F ◁ (S i).f)) → ObjectProperty.flat F)
    (hK : ∀ i, (K ⊗ (singleFunctor C 0).obj (S i).X₃).IsGE a) :
    torAmplitudeIn C a b K := by
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _, π, _, hP⟩ := L.exists_quasiIso_flat_of_isStrictlyLE b
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let e' : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
  have hPk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP
  have : P.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e'.symm a
  -- `H^{a-1}(P ⊗ S_i.X₃) = H^{a-1}(K ⊗ᴸ S_i.X₃[0]) = 0`
  have hex (i : ι) :
      (((tensorRight (S i).X₃).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) := by
    have := hK i
    have : (Q.obj (((tensorRight (S i).X₃).mapHomologicalComplex (.up ℤ)).obj P)).IsGE a :=
      TStructure.t.isGE_of_iso
        ((whiskerRightIso e' _).symm ≪≫ QObjTensorSingleFunctorObjIso P hPk (S i).X₃) a
    rw [isGE_Q_obj_iff] at this
    exact CochainComplex.exactAt_of_isGE _ a _
  have hop : ObjectProperty.flat (P.opcycles a) := hflat _ fun i ↦
    ObjectProperty.mono_opcycles_whiskerLeft_of_exactAt P a (hP _) (hP _) (S i) (hS i) (hex i)
  have : (P.truncGE a).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    obtain hi' | rfl | hi' := lt_trichotomy i a
    · exact CochainComplex.isZero_of_isStrictlyGE _ a i hi'
    · exact (P.truncGEXIsoOpcycles i).isZero_iff.2
        (IsZero.of_epi (P.pOpcycles i) (P.isZero_of_isStrictlyLE b i hi))
    · exact (P.truncGEXIso a i hi').isZero_iff.2 (P.isZero_of_isStrictlyLE b i hi)
  refine (torAmplitudeIn C a b).prop_of_iso ((asIso (Q.map (P.πTruncGE a))).symm ≪≫ e')
    (torAmplitudeIn_Q_obj_of_flat (P.truncGE a) a b fun n ↦ ?_)
  obtain hn | rfl | hn := lt_trichotomy n a
  · exact ObjectProperty.flat_of_isZero (CochainComplex.isZero_of_isStrictlyGE _ a n hn)
  · exact ObjectProperty.prop_of_iso _ (P.truncGEXIsoOpcycles n).symm hop
  · exact ObjectProperty.prop_of_iso _ (P.truncGEXIso a n hn).symm (hP n)

end DerivedCategory
