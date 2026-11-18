import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Radical
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Center
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Torus
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphismPinningStatement
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # The split pinning of type `G₂` of the split Cayley automorphism group scheme

Over every field `K`, the rank-two torus of the automorphism group scheme of Zorn's split Cayley
algebra has a reduced root datum. Its coroots span the cocharacter lattice, and for the regular
cocharacter `(1, 2)` the simple roots are the short root `u₁` and the long root `l₂₁`, with
Cartan matrix `G₂`. Together with the trivial centre this proves
`SplitCayleyAutomorphismPinningStatement` (`splitCayleyAutomorphismPinning`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsAddIndecomposable
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

/-! ### Heights for the regular cocharacter `(1, 2)` -/

/-- The pairing of the weight of a root with the cocharacter with coordinates `(1, 2)`. -/
def rootHeight (α : Root) : ℤ :=
  rootWeight α 0 + 2 * rootWeight α 1

theorem rootHeight_ne_zero (α : Root) : rootHeight α ≠ 0 := by
  cases α <;> decide

section Field

variable {K : Type u} [Field K]

set_option hygiene false in
local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))

/-! ### Roots of a root datum of the torus -/

section RootDatum

variable {J : Type u} {P : RootDatum J (characterLattice 𝕋) (cocharacterLattice 𝕋)}

theorem exists_root_eq_rootChar (hP : IsRootDatumOf (torusMap K) P) (j : J) :
    ∃ α : Root, P.root j = rootChar K α := by
  have h : P.root j ∈ roots (torusMap K) := by
    rw [← hP.2.1]
    exact ⟨j, rfl⟩
  rw [roots_torusMap] at h
  obtain ⟨α, hα⟩ := h
  exact ⟨α, hα.symm⟩

theorem exists_index_eq_rootChar (hP : IsRootDatumOf (torusMap K) P) (α : Root) :
    ∃ j : J, P.root j = rootChar K α := by
  have h : rootChar K α ∈ Set.range P.root := by
    rw [hP.2.1, roots_torusMap]
    exact ⟨α, rfl⟩
  exact h

/-- The pairing of a root with a coroot, in coordinates. -/
theorem pairing_eq_coord (hP : IsRootDatumOf (torusMap K) P) {j j' : J} {α : Root}
    (hj : P.root j = rootChar K α) :
    P.pairing j j' =
      rootWeight α 0 * GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j') 0 +
        rootWeight α 1 * GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j') 1 := by
  rw [← P.root_coroot_eq_pairing, hP.1, GeneralLinear.latticePairing_coord, hj,
    characterCoordEquiv_rootChar, Fin.sum_univ_two]

/-- Reflecting the root `β` in the root `α` gives a root, in coordinates. -/
theorem exists_reflection_coord (hP : IsRootDatumOf (torusMap K) P) {j j' : J} {α β : Root}
    (hj : P.root j = rootChar K α) (hj' : P.root j' = rootChar K β) :
    ∃ ξ : Root, ∀ c : Fin 2, rootWeight ξ c = rootWeight β c -
      (rootWeight β 0 * GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j) 0 +
        rootWeight β 1 * GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j) 1) *
          rootWeight α c := by
  obtain ⟨ξ, hξ⟩ := exists_root_eq_rootChar hP (P.reflectionPerm j j')
  refine ⟨ξ, fun c => ?_⟩
  have h := congrArg (fun χ => GeneralLinear.characterCoordEquiv (Fin 2) K χ c) hξ
  rw [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_zsmul, hj, hj',
    characterCoordEquiv_rootChar, characterCoordEquiv_rootChar, characterCoordEquiv_rootChar,
    pairing_eq_coord hP hj'] at h
  rw [← h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The coroot of the short root `u₁` has coordinates `(2, -1)`. -/
theorem corootCoord_u1 (hP : IsRootDatumOf (torusMap K) P) {j : J}
    (hj : P.root j = rootChar K .u1) :
    GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j) = ![2, -1] := by
  have h2 := P.pairing_same j
  rw [pairing_eq_coord hP hj] at h2
  obtain ⟨j', hj'⟩ := exists_index_eq_rootChar hP .l23
  obtain ⟨ξ, hξ⟩ := exists_reflection_coord hP hj hj'
  have h0 := hξ 0
  have h1 := hξ 1
  simp only [rootWeight, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  funext c
  fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      ] <;>
    cases ξ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 <;>
    omega

/-- The coroot of the long root `l₂₁` has coordinates `(-1, 1)`. -/
theorem corootCoord_l21 (hP : IsRootDatumOf (torusMap K) P) {j : J}
    (hj : P.root j = rootChar K .l21) :
    GeneralLinear.cocharacterCoordEquiv (Fin 2) K (P.coroot j) = ![-1, 1] := by
  have h2 := P.pairing_same j
  rw [pairing_eq_coord hP hj] at h2
  obtain ⟨j', hj'⟩ := exists_index_eq_rootChar hP .l13
  obtain ⟨ξ, hξ⟩ := exists_reflection_coord hP hj hj'
  have h0 := hξ 0
  have h1 := hξ 1
  simp only [rootWeight, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  funext c
  fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      ] <;>
    cases ξ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 <;>
    omega

/-- **Coroot span.** The coroots span the cocharacter lattice: the coroots `(2, -1)` of `u₁`
and `(-1, 1)` of `l₂₁` form a basis. -/
theorem corootSpan_eq_top (hP : IsRootDatumOf (torusMap K) P) : P.corootSpan ℤ = ⊤ := by
  obtain ⟨ju, hju⟩ := exists_index_eq_rootChar hP .u1
  obtain ⟨jl, hjl⟩ := exists_index_eq_rootChar hP .l21
  have hu := corootCoord_u1 hP hju
  have hl := corootCoord_l21 hP hjl
  have hmem : ∀ j : J, P.coroot j ∈ P.corootSpan ℤ := fun j => Submodule.subset_span ⟨j, rfl⟩
  rw [eq_top_iff,
    ← ((Pi.basisFun ℤ (Fin 2)).map (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).symm).span_eq,
    Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  fin_cases c
  · have h : (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).symm (Pi.single 0 1) =
        P.coroot ju + P.coroot jl := by
      apply (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).injective
      rw [LinearEquiv.apply_symm_apply, map_add, hu, hl]
      funext c
      fin_cases c <;> rfl
    rw [Fin.zero_eta, h]
    exact Submodule.add_mem _ (hmem ju) (hmem jl)
  · have h : (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).symm (Pi.single 1 1) =
        P.coroot ju + (2 : ℤ) • P.coroot jl := by
      apply (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).injective
      rw [LinearEquiv.apply_symm_apply, map_add, map_zsmul, hu, hl]
      funext c
      fin_cases c <;> rfl
    rw [Fin.mk_one, h]
    exact Submodule.add_mem _ (hmem ju) (Submodule.smul_mem _ _ (hmem jl))

/-! ### The base for the regular cocharacter -/

variable (K) in
/-- The regular cocharacter with coordinates `(1, 2)`. -/
def regularCochar : cocharacterLattice 𝕋 :=
  (GeneralLinear.cocharacterCoordEquiv (Fin 2) K).symm ![1, 2]

theorem root'_regularCochar (hP : IsRootDatumOf (torusMap K) P) {j : J} {α : Root}
    (hj : P.root j = rootChar K α) :
    P.root' j (regularCochar K) = rootHeight α := by
  change P.toLinearMap (P.root j) (regularCochar K) = _
  rw [hP.1, GeneralLinear.latticePairing_coord, hj, characterCoordEquiv_rootChar, regularCochar,
    LinearEquiv.apply_symm_apply, Fin.sum_univ_two, rootHeight]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem root'_regularCochar_ne_zero (hP : IsRootDatumOf (torusMap K) P) (j : J) :
    P.root' j (regularCochar K) ≠ 0 := by
  obtain ⟨α, hα⟩ := exists_root_eq_rootChar hP j
  rw [root'_regularCochar hP hα]
  exact rootHeight_ne_zero α

/-- A positive root which is a sum of two positive roots is not simple. -/
theorem not_mem_baseOf_of_eq_add (hP : IsRootDatumOf (torusMap K) P) {j : J} {α β ξ : Root}
    (hj : P.root j = rootChar K α) (hβ : 0 < rootHeight β) (hξ : 0 < rootHeight ξ)
    (hsum : rootWeight α = rootWeight β + rootWeight ξ) :
    j ∉ baseOf P.root ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) := by
  have hval : ∀ i : J, ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) (P.root i) =
      P.root' i (regularCochar K) := fun i => rfl
  rintro ⟨-, hind⟩
  obtain ⟨j1, hj1⟩ := exists_index_eq_rootChar hP β
  obtain ⟨j2, hj2⟩ := exists_index_eq_rootChar hP ξ
  have h1 : j1 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) (P.root i)} := by
    simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj1]
    exact hβ
  have h2 : j2 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) (P.root i)} := by
    simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj2]
    exact hξ
  have hs : P.root j = P.root j1 + P.root j2 := by
    apply (GeneralLinear.characterCoordEquiv (Fin 2) K).injective
    rw [map_add, hj, hj1, hj2, characterCoordEquiv_rootChar, characterCoordEquiv_rootChar,
      characterCoordEquiv_rootChar, hsum]
  rcases hind j1 h1 j2 h2 hs with h | h
  · exact P.ne_zero j1 h
  · exact P.ne_zero j2 h

/-- **Simple roots.** For the regular cocharacter `(1, 2)`, the indecomposable positive roots are
`u₁` and `l₂₁`. -/
theorem mem_baseOf_iff (hP : IsRootDatumOf (torusMap K) P) (j : J) :
    j ∈ baseOf P.root ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) ↔
      P.root j = rootChar K .u1 ∨ P.root j = rootChar K .l21 := by
  have hval : ∀ i : J, ((P.flip.toLinearMap (regularCochar K)) : _ →+ ℤ) (P.root i) =
      P.root' i (regularCochar K) := fun i => rfl
  have hw : ∀ α β ξ : Root, rootWeight α = rootWeight β + rootWeight ξ ↔
      (rootWeight α 0 = rootWeight β 0 + rootWeight ξ 0 ∧
        rootWeight α 1 = rootWeight β 1 + rootWeight ξ 1) := fun α β ξ => by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext c
      fin_cases c
      · exact h0
      · exact h1
  constructor
  · intro hj
    obtain ⟨α, hα⟩ := exists_root_eq_rootChar hP j
    have hpos : 0 < rootHeight α := by
      have := hj.1
      simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hα] at this
      exact this
    cases α
    · exact Or.inl hα
    · exact absurd hj (not_mem_baseOf_of_eq_add hP hα (β := .u1) (ξ := .l21) (by decide)
        (by decide) ((hw _ _ _).2 (by decide)))
    · exact absurd hpos (by decide)
    · exact absurd hpos (by decide)
    · exact absurd hpos (by decide)
    · exact absurd hj (not_mem_baseOf_of_eq_add hP hα (β := .u1) (ξ := .u2) (by decide)
        (by decide) ((hw _ _ _).2 (by decide)))
    · exact absurd hpos (by decide)
    · exact absurd hj (not_mem_baseOf_of_eq_add hP hα (β := .u1) (ξ := .v3) (by decide)
        (by decide) ((hw _ _ _).2 (by decide)))
    · exact Or.inr hα
    · exact absurd hj (not_mem_baseOf_of_eq_add hP hα (β := .l21) (ξ := .l13) (by decide)
        (by decide) ((hw _ _ _).2 (by decide)))
    · exact absurd hpos (by decide)
    · exact absurd hpos (by decide)
  · intro hj
    have hone : P.root' j (regularCochar K) = 1 := by
      rcases hj with hj | hj
      · rw [root'_regularCochar hP hj]; decide
      · rw [root'_regularCochar hP hj]; decide
    refine ⟨by simp only [Set.mem_ofPred_eq, hval, hone]; exact one_pos, ?_⟩
    intro j1 h1 j2 h2 hs
    exfalso
    have h1' : 0 < P.root' j1 (regularCochar K) := by
      simpa only [Set.mem_ofPred_eq, hval] using h1
    have h2' : 0 < P.root' j2 (regularCochar K) := by
      simpa only [Set.mem_ofPred_eq, hval] using h2
    have hsum : P.root' j (regularCochar K) =
        P.root' j1 (regularCochar K) + P.root' j2 (regularCochar K) := by
      rw [← hval, ← hval, ← hval, hs, map_add]
    omega

end RootDatum

/-! ### The pinning -/

variable (K)

/-- **Coordinate root datum.** The rank-two torus of the split Cayley automorphism group has a
reduced root datum with spanning coroots and a base numbered so that the simple pairings form
the Cartan matrix `G₂`. -/
theorem exists_coordinateRootDatum :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝕋) (cocharacterLattice 𝕋))
      (_ : IsRootDatumOf (torusMap K) P) (_ : P.IsReduced)
      (B : P.Base) (e : B.support ≃ Fin 2),
      P.corootSpan ℤ = ⊤ ∧
        ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.G₂ (e a) (e b) := by
  classical
  have : ConnectedSpace (CayleyDatum.split K).automorphismGroup.X.left :=
    connectedSpace_automorphismGroup K
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K (CayleyDatum.split K).automorphismGroup
    (isConnectedReductive K) 𝕋 (isSplitTorus_torus K) (torusMap K) (isMaximalTorus_torusMap K)
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hred
  obtain ⟨B, hB⟩ := Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P
    (regularCochar K) (root'_regularCochar_ne_zero hP)
  have hsimple : ∀ j : J, j ∈ B.support ↔
      P.root j = rootChar K .u1 ∨ P.root j = rootChar K .l21 :=
    fun j => by rw [← Finset.mem_coe, hB, mem_baseOf_iff hP]
  obtain ⟨ju, hju⟩ := exists_index_eq_rootChar hP .u1
  obtain ⟨jl, hjl⟩ := exists_index_eq_rootChar hP .l21
  have hne : rootChar K .u1 ≠ rootChar K .l21 := fun h => by
    have := rootChar_injective h
    exact Root.noConfusion this
  let g : B.support → Fin 2 := fun a => if P.root a = rootChar K .l21 then 0 else 1
  have hbij : Function.Bijective g := by
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · apply Subtype.ext
      apply P.root.injective
      have ha := (hsimple a).1 a.2
      have hb := (hsimple b).1 b.2
      by_cases ha' : P.root a = rootChar K .l21 <;> by_cases hb' : P.root b = rootChar K .l21 <;>
        simp only [g, ha', hb', ↓reduceIte] at hab
      · rw [ha', hb']
      · exact absurd hab (by decide)
      · exact absurd hab (by decide)
      · rw [ha.resolve_right ha', hb.resolve_right hb']
    · fin_cases i
      · refine ⟨⟨jl, (hsimple jl).2 (Or.inr hjl)⟩, ?_⟩
        simp only [g, hjl, ↓reduceIte]
        rfl
      · refine ⟨⟨ju, (hsimple ju).2 (Or.inl hju)⟩, ?_⟩
        simp only [g, hju, hne, ↓reduceIte]
        rfl
  refine ⟨J, hJ, P, hP, hred, B, Equiv.ofBijective g hbij, corootSpan_eq_top hP, ?_⟩
  intro a b
  have ha := (hsimple a).1 a.2
  have hb := (hsimple b).1 b.2
  simp only [Equiv.ofBijective_apply, g]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [pairing_eq_coord hP ha, corootCoord_u1 hP hb]
    simp only [ha, hb, hne, ↓reduceIte]
    decide
  · rw [pairing_eq_coord hP ha, corootCoord_l21 hP hb]
    simp only [ha, hb, hne, ↓reduceIte]
    decide
  · rw [pairing_eq_coord hP ha, corootCoord_u1 hP hb]
    simp only [ha, hb, hne, ↓reduceIte]
    decide
  · rw [pairing_eq_coord hP ha, corootCoord_l21 hP hb]
    simp only [ha, hb, ↓reduceIte]
    decide

/-- **The split pinning of type `G₂`.** Over a field, the rank-two torus of the automorphism
group scheme of Zorn's split Cayley algebra carries a split pinning whose coroots span the
cocharacter lattice and whose simple roots, numbered `l₂₁ ↦ 0` and `u₁ ↦ 1`, have Cartan
matrix `G₂`. -/
theorem exists_splitPinning :
    ∃ p : SplitPinning (CayleyDatum.split K).automorphismGroup,
      p.rootDatum.corootSpan ℤ = ⊤ ∧
        ∃ e : p.base.support ≃ Fin 2,
          ∀ a b : p.base.support, p.rootDatum.pairing a b = CartanMatrix.G₂ (e a) (e b) := by
  classical
  have : ConnectedSpace (CayleyDatum.split K).automorphismGroup.X.left :=
    connectedSpace_automorphismGroup K
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, hcartan⟩ := exists_coordinateRootDatum K
  have : Finite J := hJ
  have hG := isConnectedReductive K
  exact ⟨{ isConnectedReductive := hG
           torus := 𝕋
           inclusion := torusMap K
           isSplitTorus := isSplitTorus_torus K
           isMaximalTorus := isMaximalTorus_torusMap K
           rootIndex := J
           rootDatum := P
           isRootDatum := hP
           isReduced := hred
           base := B
           pinning := RootPinning.ofSplitMaximalTorus hG (isSplitTorus_torus K) _
             (isMaximalTorus_torusMap K) P hP B },
    hspan, e, hcartan⟩

end Field

end SplitCayley

/-- **The automorphism group of the split Cayley datum is split adjoint of type `G₂`.** Over
every field, the automorphism group scheme of Zorn's split Cayley algebra has trivial centre and
a split pinning with spanning coroots and Cartan matrix `G₂`. -/
theorem splitCayleyAutomorphismPinning : SplitCayleyAutomorphismPinningStatement.{u} :=
  fun K _ => ⟨SplitCayley.center_eq_bot K, SplitCayley.exists_splitPinning K⟩

end Langlands.GroupScheme
