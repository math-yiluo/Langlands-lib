import Langlands.Automorphic.GroupSchemeAmbient
import Langlands.Global.AdelicGroupProduct
import Langlands.Automorphic.Smooth

/-! # Finite-place regularity on actual adelic group-scheme points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Evaluation in the actual continuous rational-invariant function. -/
def evaluate (f : ContinuousRationalFunctions F G) (x : AdelicGroupPoints F G) : ℂ :=
  f.val.val x

@[simp]
theorem evaluate_rightAction (g x : AdelicGroupPoints F G)
    (f : ContinuousRationalFunctions F G) :
    evaluate F G (continuousRightAction F G g f) x = evaluate F G f (x * g) := rfl

/-- Restriction to the finite factor at a fixed infinite point. -/
def finiteSlice (a : InfiniteAdelicGroupPoints F G) :
    ContinuousRationalFunctions F G →ₗ[ℂ] (FiniteAdelicGroupPoints F G → ℂ) where
  toFun f b := evaluate F G f (AdelicGroupPoints.pair F G a b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Local constancy in each finite slice, without a uniform finite stabilizer. -/
def finiteLocallyConstantSubrepresentation :
    Subrepresentation (continuousRightAction F G) where
  toSubmodule :=
    { carrier := {f | ∀ a : InfiniteAdelicGroupPoints F G,
        IsLocallyConstant (fun b => evaluate F G f (AdelicGroupPoints.pair F G a b))}
      zero_mem' := fun _ => IsLocallyConstant.const 0
      add_mem' hf hg a := (hf a).add (hg a)
      smul_mem' c f hf a := (hf a).comp (fun z => c * z) }
  apply_mem_toSubmodule g f hf := by
    intro a
    have h := (hf (a * AdelicGroupPoints.infinite F G g)).comp_continuous
      (show Continuous (fun b : FiniteAdelicGroupPoints F G => b * AdelicGroupPoints.finite F G g)
        from continuous_id.mul continuous_const)
    simpa only [Function.comp_def, evaluate_rightAction, AdelicGroupPoints.pair_mul_right] using h

/-- Right-invariance under a specified actual finite adelic subgroup. -/
def levelSubmodule (L : Subgroup (FiniteAdelicGroupPoints F G)) :
    Submodule ℂ (ContinuousRationalFunctions F G) where
  carrier := {f | ∀ l : L, continuousRightAction F G (AdelicGroupPoints.ofFinite F G l) f = f}
  zero_mem' := by simp
  add_mem' hf hg l := by simp only [map_add, hf l, hg l]
  smul_mem' c f hf l := by simp only [map_smul, hf l]

/-- Finite level means that some actual compact open subgroup fixes the function. -/
def HasFiniteLevel (f : ContinuousRationalFunctions F G) : Prop :=
  ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
    IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
    IsCompact (L : Set (FiniteAdelicGroupPoints F G)) ∧ f ∈ levelSubmodule F G L

/-- The finite adelic right action on the continuous ambient space. -/
def finiteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (ContinuousRationalFunctions F G) :=
  (continuousRightAction F G).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

/-- Vectors with a common open finite stabilizer, stable under the full adelic action. -/
def finiteSmoothSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule := Langlands.smoothVectors (R := ℂ) (G := FiniteAdelicGroupPoints F G)
    (V := ContinuousRationalFunctions F G) (finiteRightAction F G)
  apply_mem_toSubmodule g f hf := by
    obtain ⟨L, hL⟩ := hf
    let cg : FiniteAdelicGroupPoints F G →* FiniteAdelicGroupPoints F G :=
      (MulAut.conj (AdelicGroupPoints.finite F G g)⁻¹).toMonoidHom
    have hcg : Continuous cg := IsTopologicalGroup.continuous_conj _
    refine ⟨L.comap cg hcg, ?_⟩
    intro l
    apply ((continuousRightAction F G).inv_apply_eq_iff (g := g)).mp
    have hl := hL ⟨cg l.val, l.property⟩
    change continuousRightAction F G (AdelicGroupPoints.ofFinite F G (cg l.val)) f = f at hl
    change continuousRightAction F G g⁻¹
      (continuousRightAction F G (AdelicGroupPoints.ofFinite F G l.val)
        (continuousRightAction F G g f)) = f
    change continuousRightAction F G (AdelicGroupPoints.ofFinite F G
      ((AdelicGroupPoints.finite F G g)⁻¹ * l.val * ((AdelicGroupPoints.finite F G g)⁻¹)⁻¹)) f = f at hl
    rw [inv_inv] at hl
    have hfull : continuousRightAction F G
        (g⁻¹ * AdelicGroupPoints.ofFinite F G l.val * g) f = f := by
      rw [AdelicGroupPoints.finite_conjugation]
      exact hl
    simpa only [map_mul, Module.End.mul_apply] using hfull

/-- An open finite stabilizer gives local constancy of each finite slice. -/
theorem finiteSmooth_le_finiteLocallyConstant :
    finiteSmoothSubrepresentation F G ≤ finiteLocallyConstantSubrepresentation F G := by
  intro f hf a
  obtain ⟨L, hL⟩ := hf
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro b
  refine ⟨(fun d : FiniteAdelicGroupPoints F G => b⁻¹ * d) ⁻¹' (L : Set _),
    L.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change b⁻¹ * b ∈ L
    simp
  · intro d hd
    have h := congrArg (fun f => evaluate F G f (AdelicGroupPoints.pair F G a b))
      (hL ⟨b⁻¹ * d, hd⟩)
    change evaluate F G f (AdelicGroupPoints.pair F G a b * AdelicGroupPoints.ofFinite F G (b⁻¹ * d)) =
      evaluate F G f (AdelicGroupPoints.pair F G a b) at h
    simpa only [AdelicGroupPoints.ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one,
      mul_inv_cancel_left] using h

/-- The common-open-stabilizer space, with its inherited complex vector space. -/
abbrev FiniteSmoothFunctions := (finiteSmoothSubrepresentation F G).toSubmodule

/-- The full adelic action restricts to functions with a common open finite stabilizer. -/
def finiteSmoothRightAction :
    Representation ℂ (AdelicGroupPoints F G) (FiniteSmoothFunctions F G) :=
  (finiteSmoothSubrepresentation F G).toRepresentation

/-- Common finite stabilizers give an equivariant inclusion into finite-slice regularity. -/
def finiteSmoothLocallyConstantInclusion :
    (finiteSmoothRightAction F G).IntertwiningMap
      (finiteLocallyConstantSubrepresentation F G).toRepresentation where
  toLinearMap := (finiteSmoothSubrepresentation F G).toSubmodule.inclusion
    (finiteSmooth_le_finiteLocallyConstant F G)
  isIntertwining' _ := by ext; rfl

/-- Compact finite level implies the separate open-stabilizer condition. -/
theorem hasFiniteLevel_mem_finiteSmooth (f : ContinuousRationalFunctions F G)
    (hf : HasFiniteLevel F G f) : f ∈ finiteSmoothSubrepresentation F G := by
  obtain ⟨L, ho, _, hf⟩ := hf
  exact ⟨⟨L, ho⟩, hf⟩

/-- Given an actual compact open subgroup, an open stabilizer can be shrunk to
compact finite level. Existence of that subgroup is not hidden in this lemma. -/
theorem finiteSmooth_hasFiniteLevel
    (C : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G) (hf : f ∈ finiteSmoothSubrepresentation F G) :
    HasFiniteLevel F G f := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨(C ⊓ L).toSubgroup, (C ⊓ L).isOpen, ?_, ?_⟩
  · exact hC.inter_right L.isClosed
  · intro l
    exact hL ⟨l.val, l.property.2⟩

section GeneralLinearComparison

variable (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))

local instance finiteLevelGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

@[simp]
theorem evaluate_continuousGeneralLinearEquiv
    (f : ContinuousRationalFunctions F GLG) (x : AdelicGL F n) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (continuousGeneralLinearEquiv F n f) x =
        evaluate F GLG f ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x) := rfl

/-- The ambient comparison evaluates the same function at corresponding actual points. -/
theorem evaluate_continuousGeneralLinearEquiv_at_point
    (f : ContinuousRationalFunctions F GLG) (x : AdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (continuousGeneralLinearEquiv F n f)
      (GeneralLinearGroupPoints.adelicHomeomorph F n x) = evaluate F GLG f x := by
  rw [evaluate_continuousGeneralLinearEquiv,
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm_apply_apply]

/-- Finite slices agree under the actual infinite and finite matrix comparisons. -/
theorem evaluate_continuousGeneralLinearEquiv_pair
    (f : ContinuousRationalFunctions F GLG) (a : InfiniteAdelicGroupPoints F GLG)
    (b : FiniteAdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (continuousGeneralLinearEquiv F n f)
      (AdelicGL.pair F n (GeneralLinearGroupPoints.infiniteHomeomorph F n a)
        (GeneralLinearGroupPoints.finiteHomeomorph F n b)) =
      evaluate F GLG f (AdelicGroupPoints.pair F GLG a b) := by
  rw [← GeneralLinearGroupPoints.adelicHomeomorph_pair,
    evaluate_continuousGeneralLinearEquiv_at_point]

/-- The ambient equivalence intertwines the actual finite right actions. -/
theorem continuousGeneralLinearEquiv_finiteRightAction
    (f : ContinuousRationalFunctions F GLG) (b : FiniteAdelicGroupPoints F GLG) :
    continuousGeneralLinearEquiv F n (finiteRightAction F GLG b f) =
      Langlands.Automorphic.finiteRightAction F n
        (GeneralLinearGroupPoints.finiteHomeomorph F n b)
        (continuousGeneralLinearEquiv F n f) := by
  change continuousGeneralLinearEquiv F n
    (continuousRightAction F GLG (AdelicGroupPoints.ofFinite F GLG b) f) = _
  rw [continuousGeneralLinearEquiv_rightAction,
    GeneralLinearGroupPoints.adelicHomeomorph_ofFinite]
  rfl

/-- The actual matrix comparison preserves and reflects finite-slice local constancy. -/
theorem continuousGeneralLinearEquiv_mem_finiteLocallyConstant
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.finiteLocallyConstantSubrepresentation F n ↔
      f ∈ finiteLocallyConstantSubrepresentation F GLG := by
  constructor
  · intro hf a
    have h := (hf (GeneralLinearGroupPoints.infiniteHomeomorph F n a)).comp_continuous
      (GeneralLinearGroupPoints.finiteHomeomorph F n).continuous
    change IsLocallyConstant (fun b : FiniteAdelicGroupPoints F GLG =>
      Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (continuousGeneralLinearEquiv F n f)
        (AdelicGL.pair F n (GeneralLinearGroupPoints.infiniteHomeomorph F n a)
          (GeneralLinearGroupPoints.finiteHomeomorph F n b))) at h
    simpa only [evaluate_continuousGeneralLinearEquiv_pair] using h
  · intro hf a
    obtain ⟨a, rfl⟩ := (GeneralLinearGroupPoints.infiniteHomeomorph F n).surjective a
    have h := (hf a).comp_continuous
      (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.continuous
    change IsLocallyConstant (fun b : FiniteAdelicGL F n =>
      evaluate F GLG f (AdelicGroupPoints.pair F GLG a
        ((GeneralLinearGroupPoints.finiteHomeomorph F n).symm b))) at h
    simpa only [← evaluate_continuousGeneralLinearEquiv_pair,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).apply_symm_apply] using h

/-- The finite-slice spaces are linearly equivalent through the original ambient map. -/
def finiteLocallyConstantGeneralLinearEquiv :
    (finiteLocallyConstantSubrepresentation F GLG).toSubmodule ≃ₗ[ℂ]
      (Langlands.Automorphic.finiteLocallyConstantSubrepresentation F n).toSubmodule where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_finiteLocallyConstant F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_finiteLocallyConstant F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- The finite-slice comparison retains the full adelic right action. -/
theorem finiteLocallyConstantGeneralLinearEquiv_rightAction
    (f : (finiteLocallyConstantSubrepresentation F GLG).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    finiteLocallyConstantGeneralLinearEquiv F n
        ((finiteLocallyConstantSubrepresentation F GLG).toRepresentation g f) =
      (Langlands.Automorphic.finiteLocallyConstantSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finiteLocallyConstantGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- A common open finite stabilizer is preserved and reflected by the actual matrix map. -/
theorem continuousGeneralLinearEquiv_mem_finiteSmooth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.finiteSmoothSubrepresentation F n ↔
      f ∈ finiteSmoothSubrepresentation F GLG := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).toMonoidHom
      (GeneralLinearGroupPoints.finiteHomeomorph F n).continuous, ?_⟩
    intro l
    apply (continuousGeneralLinearEquiv F n).injective
    change continuousGeneralLinearEquiv F n (finiteRightAction F GLG l.val f) = _
    rw [continuousGeneralLinearEquiv_finiteRightAction]
    exact hL ⟨GeneralLinearGroupPoints.finiteHomeomorph F n l.val, l.property⟩
  · rintro ⟨L, hL⟩
    refine ⟨L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.toMonoidHom
      (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.continuous, ?_⟩
    intro l
    have h := congrArg (continuousGeneralLinearEquiv F n)
      (hL ⟨(GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val, l.property⟩)
    change continuousGeneralLinearEquiv F n
      (finiteRightAction F GLG ((GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val) f) =
        continuousGeneralLinearEquiv F n f at h
    rw [continuousGeneralLinearEquiv_finiteRightAction,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).apply_symm_apply] at h
    exact h

/-- The common-open-stabilizer spaces agree without imposing infinite smoothness. -/
def finiteSmoothGeneralLinearEquiv :
    FiniteSmoothFunctions F GLG ≃ₗ[ℂ]
      (Langlands.Automorphic.finiteSmoothSubrepresentation F n).toSubmodule where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_finiteSmooth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_finiteSmooth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- The common-stabilizer comparison retains the full adelic right action. -/
theorem finiteSmoothGeneralLinearEquiv_rightAction
    (f : FiniteSmoothFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    finiteSmoothGeneralLinearEquiv F n (finiteSmoothRightAction F GLG g f) =
      (Langlands.Automorphic.finiteSmoothSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finiteSmoothGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- Fixed finite levels correspond by inverse image under the actual finite point map. -/
theorem continuousGeneralLinearEquiv_mem_levelSubmodule
    (L : Subgroup (FiniteAdelicGL F n)) (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈ Langlands.Automorphic.levelSubmodule F n L ↔
      f ∈ levelSubmodule F GLG
        (L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).toMonoidHom) := by
  constructor
  · intro hf l
    apply (continuousGeneralLinearEquiv F n).injective
    change continuousGeneralLinearEquiv F n (finiteRightAction F GLG l.val f) = _
    rw [continuousGeneralLinearEquiv_finiteRightAction]
    exact hf ⟨GeneralLinearGroupPoints.finiteHomeomorph F n l.val, l.property⟩
  · intro hf l
    have hl : GeneralLinearGroupPoints.finiteHomeomorph F n
        ((GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val) ∈ L := by
      simpa only [(GeneralLinearGroupPoints.finiteHomeomorph F n).apply_symm_apply] using
        l.property
    have h := congrArg (continuousGeneralLinearEquiv F n)
      (hf ⟨(GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val, hl⟩)
    change continuousGeneralLinearEquiv F n
      (finiteRightAction F GLG ((GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val) f) =
        continuousGeneralLinearEquiv F n f at h
    rw [continuousGeneralLinearEquiv_finiteRightAction,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).apply_symm_apply] at h
    exact h

/-- Fixed-level spaces correspond through the same ambient linear equivalence. -/
def levelGeneralLinearEquiv (L : Subgroup (FiniteAdelicGL F n)) :
    levelSubmodule F GLG
        (L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).toMonoidHom) ≃ₗ[ℂ]
      Langlands.Automorphic.levelSubmodule F n L where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_levelSubmodule F n L f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_levelSubmodule F n L _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- Compact open finite level is the same predicate on the original matrix space. -/
theorem continuousGeneralLinearEquiv_hasFiniteLevel
    (f : ContinuousRationalFunctions F GLG) :
    Langlands.Automorphic.HasFiniteLevel F n (continuousGeneralLinearEquiv F n f) ↔
      HasFiniteLevel F GLG f := by
  constructor
  · rintro ⟨L, ho, hc, hf⟩
    refine ⟨L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).toMonoidHom,
      ho.preimage (GeneralLinearGroupPoints.finiteHomeomorph F n).continuous,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).toHomeomorph.isCompact_preimage.mpr hc,
      (continuousGeneralLinearEquiv_mem_levelSubmodule F n L f).mp hf⟩
  · rintro ⟨L, ho, hc, hf⟩
    refine ⟨L.comap (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.toMonoidHom,
      ho.preimage (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.continuous,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).symm.toHomeomorph.isCompact_preimage.mpr hc,
      ?_⟩
    intro l
    have h := congrArg (continuousGeneralLinearEquiv F n)
      (hf ⟨(GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val, l.property⟩)
    change continuousGeneralLinearEquiv F n
      (finiteRightAction F GLG ((GeneralLinearGroupPoints.finiteHomeomorph F n).symm l.val) f) =
        continuousGeneralLinearEquiv F n f at h
    rw [continuousGeneralLinearEquiv_finiteRightAction,
      (GeneralLinearGroupPoints.finiteHomeomorph F n).apply_symm_apply] at h
    exact h

end GeneralLinearComparison

end Langlands.Automorphic.GroupSchemeFunctions
