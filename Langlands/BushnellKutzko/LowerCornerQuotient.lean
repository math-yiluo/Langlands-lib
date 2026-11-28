import Langlands.BushnellKutzko.LowerBlockSubgroup
import Langlands.BushnellKutzko.SimpleHLayerCentralizer
import Langlands.BushnellKutzko.BlockLatticeCharacter

/-! # The lower-corner quotient of the intermediate split-type subgroup

On the subgroup of `H^m` with lower corner in `𝔓^(m+1)`, projecting to that
corner and multiplying on the right by an element of `𝔔⁻¹` gives the kernel
test for a finite quotient. The construction adapts the lower-corner comparison
of BK93 (8.2.26) to this subgroup. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The lower-corner map `x ↦ e₂ x e₁` followed by right multiplication by `ζ'`. -/
def lowerCornerShift (e₁ e₂ ζ' : A) : A →ₗ[𝒪[F]] A :=
  (LinearMap.mulRight 𝒪[F] ζ').comp
    ((LinearMap.mulRight 𝒪[F] e₁).comp (LinearMap.mulLeft 𝒪[F] e₂))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem lowerCornerShift_apply (e₁ e₂ ζ' x : A) :
    lowerCornerShift e₁ e₂ ζ' x = e₂ * x * e₁ * ζ' :=
  rfl

/-- The quotient of `T` detecting whether the shifted lower corner belongs to `X`. -/
abbrev lowerCornerQuotient (T X : Submodule 𝒪[F] A) (e₁ e₂ ζ' : A) :=
  T ⧸ X.comap ((lowerCornerShift e₁ e₂ ζ').comp T.subtype)

section Simple

variable (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
  {e₁ e₂ ζ' : Module.End F V} (hadd : e₁ + e₂ = 1)
  (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0)
  (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
  (m : ℕ) (hm : 1 ≤ m)

local notation "H" k => simpleHLayer S.chain S.n S.b q.tail k

/-- The depth-`m` H subgroup with one extra step of depth in the lower corner. -/
abbrev lowerBlockSimpleHGroup :=
  lowerBlockSubgroup S.chain hadd he₁.1 he₂.1 (simpleHGroup S.chain S.n S.b q.tail m) m hm
    (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail m)

local notation "K" => lowerBlockSimpleHGroup S q hadd he₁ he₂ m hm

/-- The lower corner of an element of the intermediate subgroup, in the next H layer. -/
def lowerCornerRepresentative (h0 : S.r = 0) (hs : S.IsSimple) (k : K) : H (m + 1) := by
  have hk : (k : G) ∈ simpleHGroup S.chain S.n S.b q.tail m := k.property.1
  have hkH := (simpleHGroup_mem_iff_of_pos S h0 hs q hm).mp hk
  have hleft := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₂ hkH).1
  have hboth := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₁ hleft).2
  exact ⟨e₂ * ((k : G) - 1 : A) * e₁, hboth.1, k.property.2⟩

variable (h0 : S.r = 0) (hs : S.IsSimple)
  (X : Submodule 𝒪[F] (Module.End F V))
  (hX : simpleHLayer S.chain S.n S.b q.tail m ≤ X)
  (hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1))

local notation "Y" => lowerCornerQuotient (H (m + 1)) X e₁ e₂ ζ'
local notation "rep" => lowerCornerRepresentative S q hadd he₁ he₂ m hm h0 hs

/-- The lower-corner map is a group homomorphism because the shifted quadratic
term lies in `𝔥^m`, which is contained in the denominator. -/
def lowerCornerQuotientHom : K →* Multiplicative Y where
  toFun k := Multiplicative.ofAdd (Submodule.Quotient.mk (rep k))
  map_one' := by
    change Submodule.Quotient.mk (rep 1) = (0 : Y)
    rw [Submodule.Quotient.mk_eq_zero]
    change lowerCornerShift e₁ e₂ ζ' (e₂ * (((1 : G) : A) - 1) * e₁) ∈ X
    simp
  map_mul' k l := by
    change Submodule.Quotient.mk (rep (k * l)) = (Submodule.Quotient.mk (rep k + rep l) : Y)
    apply (Submodule.Quotient.eq _).mpr
    let x : A := (k : G) - 1
    let y : A := (l : G) - 1
    have hx : x ∈ H m := (simpleHGroup_mem_iff_of_pos S h0 hs q hm).mp k.property.1
    have hy : y ∈ H m := (simpleHGroup_mem_iff_of_pos S h0 hs q hm).mp l.property.1
    change lowerCornerShift e₁ e₂ ζ'
      (e₂ * (((k : G) * (l : G) : G) - 1 : A) * e₁ - (e₂ * x * e₁ + e₂ * y * e₁)) ∈ X
    have hcross : e₂ * (((k : G) * (l : G) : G) - 1 : A) * e₁ -
        (e₂ * x * e₁ + e₂ * y * e₁) = e₂ * x * y * e₁ := by
      dsimp [x, y]
      noncomm_ring
    rw [hcross, lowerCornerShift_apply]
    have hx' := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₂
      (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₂ hx).1).1
    have hy' := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₁
      (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q m he₁ hy).2).2
    rw [show e₂ * (e₂ * x * y * e₁) * e₁ * ζ' =
      (e₂ * (e₂ * x)) * (y * e₁ * e₁) * ζ' by noncomm_ring]
    exact hX (mul_mul_mem_simpleHLayer_of_inv S h0 hs q hm hζ' hx' hy').2.2

theorem lowerCornerQuotientHom_apply (k : K) :
    lowerCornerQuotientHom S q hadd he₁ he₂ m hm h0 hs X hX hζ' k =
      Multiplicative.ofAdd (Submodule.Quotient.mk (rep k)) :=
  rfl

theorem lowerCornerQuotientHom_eq_one (h₁ : e₁ * e₁ = e₁) (h₂ : e₂ * e₂ = e₂) (k : K) :
    lowerCornerQuotientHom S q hadd he₁ he₂ m hm h0 hs X hX hζ' k = 1 ↔
      e₂ * ((k : G) - 1 : A) * e₁ * ζ' ∈ X := by
  change Submodule.Quotient.mk (rep k) = (0 : Y) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change e₂ * (e₂ * ((k : G) - 1 : A) * e₁) * e₁ * ζ' ∈ X ↔ _
  rw [show e₂ * (e₂ * ((k : G) - 1 : A) * e₁) * e₁ * ζ' =
    (e₂ * e₂) * ((k : G) - 1 : A) * (e₁ * e₁) * ζ' by noncomm_ring, h₁, h₂]

theorem lowerCornerQuotientHom_surjective (h₁₂ : e₁ * e₂ = 0)
    (h₁ : e₁ * e₁ = e₁) (h₂ : e₂ * e₂ = e₂) :
    Function.Surjective (lowerCornerQuotientHom S q hadd he₁ he₂ m hm h0 hs X hX hζ') := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd y)
  let g := blockUnit e₂ e₁ h₁₂ (x : A)
  have hgsub : (g : A) - 1 = e₂ * (x : A) * e₁ := by
    rw [blockUnit_val, add_sub_cancel_left]
  have hleft := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (m + 1) he₂ x.property).1
  have hgT : (g : A) - 1 ∈ H (m + 1) := by
    rw [hgsub]
    exact (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (m + 1) he₁ hleft).2
  have hproj (a : A) : e₂ * (e₂ * a * e₁) * e₁ = e₂ * a * e₁ := by
    calc e₂ * (e₂ * a * e₁) * e₁ = (e₂ * e₂) * a * (e₁ * e₁) := by noncomm_ring
      _ = _ := by rw [h₁, h₂]
  let k : K := ⟨g, (simpleHGroup_mem_iff_of_pos S h0 hs q hm).mpr
    ⟨hgT.1, S.chain.endFiltration_antitone (by push_cast; omega) hgT.2⟩, by
      rw [hgsub, hproj, ← hgsub]
      exact hgT.2⟩
  refine ⟨k, ?_⟩
  change Submodule.Quotient.mk (rep k) = Multiplicative.toAdd y
  rw [← hx]
  apply (Submodule.Quotient.eq _).mpr
  change lowerCornerShift e₁ e₂ ζ'
    (e₂ * ((g : A) - 1) * e₁ - (x : A)) ∈ X
  rw [map_sub, hgsub, hproj]
  simp only [lowerCornerShift_apply, hproj, sub_self, zero_mem]

end Simple

/-- Finiteness of the quotient from the ambient lattice filtration. -/
theorem finite_lowerCornerQuotient (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
    (h0 : S.r = 0) (hs : S.IsSimple) (m : ℕ) (X : Submodule 𝒪[F] A)
    (hX : simpleHLayer S.chain S.n S.b q.tail m ≤ X) {e₁ e₂ ζ' : A}
    (he₁ : e₁ ∈ S.chain.endFiltration 0) (he₂ : e₂ ∈ S.chain.endFiltration 0)
    (hζ' : ζ' ∈ S.chain.endFiltration (-1)) :
    Finite (lowerCornerQuotient (simpleHLayer S.chain S.n S.b q.tail (m + 1)) X e₁ e₂ ζ') := by
  let T := simpleHLayer S.chain S.n S.b q.tail (m + 1)
  let N := max S.n (m : ℤ) + 1
  have hN : 0 ≤ N := by dsimp [N]; have := le_max_right S.n (m : ℤ); omega
  have hT : T ≤ S.chain.endFiltration 0 :=
    inf_le_right.trans (S.chain.endFiltration_antitone (by push_cast; omega))
  let : Finite (latticeQuotient S.chain T N) := finite_latticeQuotient S.chain hT hN
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hbound := (sequence_for_simple S h0 hs q).simpleHLayer_bounds hn m
  have hle : (S.chain.endFiltration N).comap T.subtype ≤
      X.comap ((lowerCornerShift e₁ e₂ ζ').comp T.subtype) := by
    intro x hx
    change (x : A) ∈ S.chain.endFiltration N at hx
    change e₂ * (x : A) * e₁ * ζ' ∈ X
    apply hX
    apply hbound.1
    exact mul_mul_mem_endFiltration S.chain (S.chain.mul_mem_endFiltration he₂ hx) he₁ hζ'
      (by dsimp [N]; ring)
  apply Finite.of_surjective (Submodule.factor hle)
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The shifted lower corner gives a finite abelian quotient of the intermediate
H subgroup, with kernel determined by the chosen denominator lattice. -/
def LowerCornerQuotientStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (e₁ e₂ ζ' : Module.End F V) (hadd : e₁ + e₂ = 1), e₁ * e₂ = 0 →
    ∀ (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0)
      (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
      (hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1))
      (m : ℕ) (hm : 1 ≤ m) (X : Submodule 𝒪[F] (Module.End F V))
      (hX : simpleHLayer S.chain S.n S.b q.tail m ≤ X),
      let Y := lowerCornerQuotient (simpleHLayer S.chain S.n S.b q.tail (m + 1)) X e₁ e₂ ζ'
      let p := lowerCornerQuotientHom S q hadd he₁ he₂ m hm h0 hs X hX hζ'
      Finite Y ∧ Function.Surjective p ∧
        ∀ k, p k = 1 ↔ e₂ * ((k : (Module.End F V)ˣ) - 1 : Module.End F V) * e₁ * ζ' ∈ X

theorem lowerCornerQuotientProperties : LowerCornerQuotientStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ S h0 hs q e₁ e₂ ζ' hadd h₁₂ he₁ he₂ hζ' m hm X hX
  have h₁ : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, h₁₂, add_zero]
      _ = e₁ := by rw [hadd, mul_one]
  have h₂ : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, h₁₂, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  exact ⟨finite_lowerCornerQuotient S q h0 hs m X hX he₁.1 he₂.1 hζ'.1,
    lowerCornerQuotientHom_surjective S q hadd he₁ he₂ m hm h0 hs X hX hζ' h₁₂ h₁ h₂,
    lowerCornerQuotientHom_eq_one S q hadd he₁ he₂ m hm h0 hs X hX hζ' h₁ h₂⟩

end Langlands.BushnellKutzko.SplitBlocks
