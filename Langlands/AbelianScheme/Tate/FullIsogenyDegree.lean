import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.IsogenyFinrankKernelCardProof
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.Degree
import Langlands.AbelianScheme.Tate.FullSeparation

/-! # The full integral Tate cokernel of an isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

namespace Langlands.AbelianScheme.Tate

open Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B) (hf : IsIsogeny f)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (s : Spec (.of Ω) ⟶ S)

local notation "T" => Over.mk s
local notation "P" => (fun _ : ℕ => True)
local notation "φ" => GroupScheme.pointsHom (groupHom f) T
local notation "GA" => A.toGrp
local notation "GB" => B.toGrp
local notation "mapf" => Langlands.GroupScheme.Tate.map T P (groupHom f)
local notation "coord" G:max i:max x:max =>
  toSection G T (i).val (evaluation G T P i x)

include hf in
private theorem geometric_fullCokernel_nonempty :
    Nonempty ((Full GB T ⧸ (mapf).range) ≃+ Additive (φ).ker) := by
  obtain ⟨n, hn, _, ψ, hφψ, hψφ⟩ := GroupScheme.exists_pow_quasiInverse φ
    (hf.pointsHom_surjective s) (hf.finite_ker_pointsHom s)
  let N : Index P := ⟨n, hn, trivial⟩
  let j (i : Index P) : Index P := ⟨n * i.val, Nat.mul_pos hn i.property.1, trivial⟩
  let boundaryPoints : Full GB T →+ Additive (T ⟶ (GA).X) :=
    ψ.toAdditive.comp ((toSection GB T n).comp (evaluation GB T P N))
  have hker (y : Full GB T) : Additive.toMul (boundaryPoints y) ∈ (φ).ker := by
    change φ (ψ (Additive.toMul (coord GB N y))) = 1
    rw [hφψ]
    exact (mem_levelGroup GB T n _).mp (Additive.toMul (evaluation GB T P N y)).property
  let boundary : Full GB T →+ Additive (φ).ker :=
    { toFun := fun y => Additive.ofMul ⟨Additive.toMul (boundaryPoints y), hker y⟩
      map_zero' := Subtype.ext (map_zero boundaryPoints)
      map_add' := fun y z => Subtype.ext (map_add boundaryPoints y z) }
  have hsurj : Function.Surjective boundary := by
    intro x
    obtain ⟨a, ha⟩ := algClosedPointDivisibility S A Ω s n
      (Nat.cast_ne_zero.mpr hn.ne') (Additive.toMul x).val
    have hx : ψ (φ a) = (Additive.toMul x).val := (hψφ a).trans ha
    have hφa : φ a ∈ levelGroup GB T n := by
      rw [mem_levelGroup, ← hφψ, hx]
      exact (Additive.toMul x).property
    have hv := full_evaluation_surjective_of_pow GB T
      (fun k hk => algClosedPointDivisibility S B Ω s k (Nat.cast_ne_zero.mpr hk.ne')) N
    obtain ⟨y, hy⟩ := hv (Additive.ofMul ⟨φ a, hφa⟩)
    refine ⟨y, Subtype.ext ?_⟩
    change ψ (Additive.toMul (coord GB N y)) = (Additive.toMul x).val
    rw [hy]
    exact hx
  have hexact : (mapf).range = boundary.ker := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      apply AddMonoidHom.mem_ker.mpr
      apply Subtype.ext
      change ψ (φ (Additive.toMul (coord GA N a))) = 1
      rw [hψφ]
      exact (mem_levelGroup GA T n _).mp (Additive.toMul (evaluation GA T P N a)).property
    · intro hy
      have hzero : boundaryPoints y = 0 :=
        congrArg (fun z : Additive (φ).ker => Additive.ofMul (Additive.toMul z).val)
          (AddMonoidHom.mem_ker.mp hy)
      have hcoord (i k : Index P) (hik : i.val ∣ k.val) :
          (k.val / i.val) • coord GB k y = coord GB i y := by
        rw [← toSection_transition GB T hik, evaluation_transition]
      have hmem (i : Index P) :
          ψ (Additive.toMul (coord GB (j i) y)) ∈ levelGroup GA T i.val := by
        rw [mem_levelGroup]
        have h := hcoord N (j i) (dvd_mul_right n i.val)
        change (n * i.val / n) • coord GB (j i) y = coord GB N y at h
        rw [Nat.mul_div_cancel_left _ hn] at h
        change Additive.toMul (i.val • ψ.toAdditive (coord GB (j i) y)) = 1
        rw [← map_nsmul, h]
        exact congrArg Additive.toMul hzero
      let preimage : Full GA T := ⟨fun i =>
          Additive.ofMul ⟨ψ (Additive.toMul (coord GB (j i) y)), hmem i⟩, by
        intro i k hik
        apply toSection_injective GA T i.val
        rw [toSection_transition]
        change (k.val / i.val) • ψ.toAdditive (coord GB (j k) y) =
          ψ.toAdditive (coord GB (j i) y)
        have h := hcoord (j i) (j k) (Nat.mul_dvd_mul_left n hik)
        change ((n * k.val) / (n * i.val)) • coord GB (j k) y = _ at h
        rw [Nat.mul_div_mul_left _ _ hn] at h
        rw [← map_nsmul, h]⟩
      refine ⟨preimage, ?_⟩
      apply Subtype.ext
      funext i
      apply toSection_injective GB T i.val
      change Additive.ofMul (φ (ψ (Additive.toMul (coord GB (j i) y)))) = coord GB i y
      rw [hφψ]
      change n • coord GB (j i) y = coord GB i y
      have h := hcoord i (j i) (dvd_mul_left i.val n)
      change (n * i.val / i.val) • coord GB (j i) y = _ at h
      rwa [Nat.mul_div_cancel _ i.property.1] at h
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hexact).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective boundary hsurj)⟩

/-- The full integral Tate cokernel at an algebraically closed point in
characteristic zero is additively equivalent to the geometric point kernel. -/
def fullIsogenyCokernelEquiv :
    (Full GB T ⧸ (mapf).range) ≃+ Additive (φ).ker :=
  Classical.choice (geometric_fullCokernel_nonempty f hf s)

/-- Over an algebraically closed field of characteristic zero the native
isogeny rank is the cardinality of its full integral Tate cokernel. -/
theorem finrank_eq_card_fullIsogenyCokernel
    (A' B' : AbelianScheme (Spec (.of Ω))) (f' : A' ⟶ B') (hf' : IsIsogeny f')
    (y : B'.X.left) :
    (hom f').finrank y =
      Nat.card (Full B'.toGrp (Over.mk (𝟙 _)) ⧸
        (Langlands.GroupScheme.Tate.map (Over.mk (𝟙 _)) P (groupHom f')).range) :=
  (isogenyFinrankKernelCard Ω A' B' f' hf' y).trans
    (Nat.card_congr (fullIsogenyCokernelEquiv f' hf' (𝟙 _)).toEquiv).symm

include hf in
/-- At a point of the geometric fibre of the target over `s`, the native
rank of the original isogeny is computed by its full Tate cokernel at `s`. -/
theorem finrank_eq_card_fullIsogenyCokernel_at
    (y : ((baseChange s).obj B).X.left) :
    (hom f).finrank (pullback.fst B.X.hom s y) =
      Nat.card (Full GB T ⧸ (mapf).range) := by
  let t := Over.mk (𝟙 (Spec (.of Ω)))
  let f' := (baseChange s).map f
  let e : (Over.map s).obj t ≅ T := Over.isoMk (Iso.refl _) (by simp [t])
  let K := (GroupScheme.kernel (groupHom f)).X
  have ek :
      (GroupScheme.pointsHom (groupHom f') t).ker ≃ (φ).ker :=
    (GroupScheme.baseChangeKernelPointsEquiv s (groupHom f) t).toEquiv.trans
      ((GroupScheme.kernelPointsEquiv (groupHom f) ((Over.map s).obj t)).symm.toEquiv.trans
        ((Iso.homCongr e (Iso.refl K)).trans
          (GroupScheme.kernelPointsEquiv (groupHom f) T).toEquiv))
  have : IsFinite (hom f) := hf.1
  have : Flat (hom f) := hf.2.1
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _
    (PolarizedFiniteLevel.hom_baseChange_isPullback s f) y).symm.trans
    ((isogenyFinrankKernelCard Ω _ _ f' (hf.baseChange s) y).trans
      ((Nat.card_congr ek).trans
        (Nat.card_congr (fullIsogenyCokernelEquiv f hf s).toEquiv).symm))

end Langlands.AbelianScheme.Tate
