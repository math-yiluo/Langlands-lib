import Langlands.Algebra.DirectedModuleFlatnessAscentStatement
import Langlands.Algebra.LocalApproximationResidueFiber
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Colimit.Module
import Mathlib.Data.Fintype.Order

namespace Langlands.Algebra
namespace DirectedModuleFlatnessAscentProof

universe uI uA uP uR uM uK uB uS

/-- A finite collection of elements in a directed cocone lifts to one component. -/
theorem finite_lift
    {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type uA} {R : Type uR}
    (f : ∀ i j, i ≤ j → A i → A j) (g : ∀ i, A i → R)
    (hg : ∀ i j h x, g j (f i j h x) = g i x)
    (hsurj : ∀ r, ∃ i x, g i x = r)
    {κ : Type uK} [Finite κ] (r : κ → R) :
    ∃ (i : ι) (a : κ → A i), ∀ k, g i (a k) = r k := by
  classical
  choose i a ha using fun k ↦ hsurj (r k)
  obtain ⟨j, hj⟩ := Finite.exists_le i
  exact ⟨j, fun k ↦ f (i k) j (hj k) (a k), fun k ↦ (hg _ _ _ _).trans (ha k)⟩

/-- Trivial finite relations push forward along a semilinear map. -/
theorem map_trivial_relation
    {A : Type uA} {P : Type uP} {R : Type uR} {M : Type uM}
    [CommRing A] [AddCommGroup P] [Module A P]
    [CommRing R] [AddCommGroup M] [Module R M]
    (g : A →+* R) (q : P →+ M)
    (hq : ∀ a x, q (a • x) = g a • q x)
    {κ : Type uK} [Fintype κ] {a : κ → A} {x : κ → P}
    (h : Module.IsTrivialRelation a x) :
    Module.IsTrivialRelation (fun k ↦ g (a k)) (fun k ↦ q (x k)) := by
  obtain ⟨n, b, y, hxy, hab⟩ := h
  refine ⟨n, fun k j ↦ g (b k j), fun j ↦ q (y j), ?_, ?_⟩
  · intro k
    change q (x k) = ∑ j, g (b k j) • q (y j)
    rw [hxy k, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ hq _ _
  · intro j
    simpa only [map_sum, map_mul, map_zero] using congrArg g (hab j)

/-- Raw equational ascent, with the representative and eventual-zero consequences of a colimit. -/
theorem flat_of_representatives
    {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A : ι → Type uA) (P : ι → Type uP)
    [∀ i, CommRing (A i)] [∀ i, AddCommGroup (P i)] [∀ i, Module (A i) (P i)]
    (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (t : ∀ i j, i ≤ j → P i →+ P j)
    (ht : ∀ i j h a x, t i j h (a • x) = f i j h a • t i j h x)
    (g : ∀ i, A i →+* R) (q : ∀ i, P i →+ M)
    (hg : ∀ i j h a, g j (f i j h a) = g i a)
    (hq : ∀ i j h x, q j (t i j h x) = q i x)
    (hsmul : ∀ i a x, q i (a • x) = g i a • q i x)
    (hR : ∀ r, ∃ i a, g i a = r)
    (hM : ∀ m, ∃ i x, q i x = m)
    (hzero : ∀ i x, q i x = 0 → ∃ (j : ι) (h : i ≤ j), t i j h x = 0)
    (hflat : ∀ i, ∃ j, i ≤ j ∧ Module.Flat (A j) (P j)) :
    Module.Flat R M := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n a x hax
  obtain ⟨i, ai, hai⟩ := finite_lift (fun i j h ↦ f i j h) (fun i ↦ g i) hg hR a
  obtain ⟨j, xj, hxj⟩ := finite_lift (fun i j h ↦ t i j h) (fun i ↦ q i) hq hM x
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let ak : Fin n → A k := fun l ↦ f i k hik (ai l)
  let xk : Fin n → P k := fun l ↦ t j k hjk (xj l)
  have hak : ∀ l, g k (ak l) = a l := fun l ↦ (hg _ _ _ _).trans (hai l)
  have hxk : ∀ l, q k (xk l) = x l := fun l ↦ (hq _ _ _ _).trans (hxj l)
  have hqrel : q k (∑ l, ak l • xk l) = 0 := by
    simpa only [map_sum, hsmul, hak, hxk] using hax
  obtain ⟨k', hkk', hrel⟩ := hzero k _ hqrel
  obtain ⟨k'', hk'k'', hfl⟩ := hflat k'
  let := hfl
  let a' : Fin n → A k'' := fun l ↦ f k' k'' hk'k'' (f k k' hkk' (ak l))
  let x' : Fin n → P k'' := fun l ↦ t k' k'' hk'k'' (t k k' hkk' (xk l))
  have hrel' : ∑ l, a' l • x' l = 0 := by
    have := congrArg (t k' k'' hk'k'') hrel
    simpa only [map_sum, ht, map_zero, a', x'] using this
  have htriv := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel'
  have hmap := map_trivial_relation (g k'') (q k'') (hsmul k'') htriv
  simpa only [a', x', hg, hq, hak, hxk] using hmap

/-- Flatness of a varying-ring directed colimit with eventually flat components. -/
theorem flat_of_colimit
    {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A : ι → Type uA) (P : ι → Type uP)
    [∀ i, CommRing (A i)] [∀ i, AddCommGroup (P i)] [∀ i, Module (A i) (P i)]
    (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (t : ∀ i j, i ≤ j → P i →+ P j)
    [DirectedSystem P (fun i j h ↦ t i j h)]
    (ht : ∀ i j h a x, t i j h (a • x) = f i j h a • t i j h x)
    (g : ∀ i, A i →+* R) (q : ∀ i, P i →+ M)
    (hg : ∀ i j h a, g j (f i j h a) = g i a)
    (hq : ∀ i j h x, q j (t i j h x) = q i x)
    (hsmul : ∀ i a x, q i (a • x) = g i a • q i x)
    (hR : Function.Bijective (Ring.DirectLimit.lift A (fun i j h ↦ f i j h) R g hg))
    (hM : Function.Bijective
      (@AddCommGroup.DirectLimit.lift ι _ P _ t (Classical.decEq ι) M _ q hq))
    (hflat : ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (A j) (P j)) :
    Module.Flat R M := by
  classical
  apply flat_of_representatives A P R M f t ht g q hg hq hsmul
  · intro r
    obtain ⟨z, hz⟩ := hR.2 r
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of z
    exact ⟨i, a, by simpa only [Ring.DirectLimit.lift_of] using hz⟩
  · intro m
    obtain ⟨z, hz⟩ := hM.2 m
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i x =>
      exact ⟨i, x, by simpa only [AddCommGroup.DirectLimit.lift_of] using hz⟩
  · intro i x hx
    apply AddCommGroup.DirectLimit.of.zero_exact i x
    apply hM.1
    simpa only [AddCommGroup.DirectLimit.lift_of, map_zero] using hx
  · intro i
    obtain ⟨i₀, hi₀⟩ := hflat
    obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀
    exact ⟨j, hij, hi₀ j hi₀j⟩

end DirectedModuleFlatnessAscentProof

universe uI uA uP uR uM uB uS

/-- Eventual component flatness ascends through the actual varying-ring colimit. -/
theorem directedModuleFlatnessAscent :
    DirectedModuleFlatnessAscentStatement.{uI, uA, uP, uR, uM} := by
  intro ι _ _ _ R M _ _ _ D hD hflat
  let : DirectedSystem D.obj
      (fun i j h ↦ (D.map i j h).toAddMonoidHom) := D.directed
  exact DirectedModuleFlatnessAscentProof.flat_of_colimit D.base D.obj R M
    D.baseMap (fun i j h ↦ (D.map i j h).toAddMonoidHom)
    (fun i j h a x ↦ (D.map i j h).map_smulₛₗ a x)
    D.baseι (fun i ↦ (D.ιM i).toAddMonoidHom)
    D.baseι_compat D.ιM_compat
    (fun i a x ↦ (D.ιM i).map_smulₛₗ a x) hD.1 hD.2 hflat

namespace LocalModuleSystem

open scoped Langlands.Algebra.LocalModuleSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The published base-scalar adapter transfers generic flatness ascent to local systems. -/
theorem flat_of_eventually_flat
    (E : LocalModuleSystem.{uI, uA, uB, uP, uR, uS, uM} D M)
    (hE : E.IsColimit)
    (hflat : ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.base j) (E.obj j)) :
    Module.Flat R M :=
  directedModuleFlatnessAscent ι R M E.toDirectedModuleSystem
    ⟨hE.1.1, hE.2⟩ hflat

end LocalModuleSystem

end Langlands.Algebra
