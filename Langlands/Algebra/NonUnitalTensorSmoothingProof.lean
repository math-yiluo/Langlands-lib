import Langlands.Algebra.NonUnitalTensorSmoothingStatements

/-!
# Prescribed additive tensor smoothing and naturality

The exact closed tensor-smoothing statement for Renard I.4.3, proved from the
published inclusion, every-fixer reverse formula and original tensor balancing.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalTensorSmoothingProof

open MulOpposite NonUnitalModuleTensor NonUnitalTensorSmoothing
open NonUnitalTensorSmoothingStatements

universe uA uN uM uN' uM'

section Components

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hM : IsNondegenerate A M)

/-- Both prescribed maps are inverse as entire additive maps. -/
theorem inverseIdentities : InverseIdentities hA N hM := by
  constructor
  · apply hom_ext A
    intro n m
    obtain ⟨e, he⟩ := hM m
    change reverse hA N hM (inclusion hA N M
      (tmul A (nondegeneratePart hA.op N) M n m)) =
        tmul A (nondegeneratePart hA.op N) M n m
    rw [inclusion_tmul, reverse_tmul hA N hM (n : N) m e he]
    change tmul A (nondegeneratePart hA.op N) M (op (e : A) • n) m =
      tmul A (nondegeneratePart hA.op N) M n m
    rw [tmul_balanced, he]
  · apply hom_ext A
    intro n m
    obtain ⟨e, he⟩ := hM m
    change inclusion hA N M (reverse hA N hM (tmul A N M n m)) = tmul A N M n m
    rw [reverse_tmul hA N hM n m e he, inclusion_tmul]
    change tmul A N M (op (e : A) • n) m = tmul A N M n m
    rw [tmul_balanced, he]

/-- Bijectivity is a consequence of the proved whole-map identities. -/
theorem bijectivity : Bijectivity hA N hM := by
  have hi := inverseIdentities hA N hM
  have hleft : Function.LeftInverse (reverse hA N hM) (inclusion hA N M) :=
    fun t => DFunLike.congr_fun hi.1 t
  have hright : Function.LeftInverse (inclusion hA N M) (reverse hA N hM) :=
    fun t => DFunLike.congr_fun hi.2 t
  exact ⟨⟨hleft.injective, hright.surjective⟩, ⟨hright.injective, hleft.surjective⟩⟩

/-- The equivalence uses precisely the published maps and all their generator formulas. -/
theorem prescribedEquivalence : PrescribedEquivalence hA N hM := by
  have hi := inverseIdentities hA N hM
  let E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M :=
    { toFun := inclusion hA N M
      invFun := reverse hA N hM
      left_inv := fun t => DFunLike.congr_fun hi.1 t
      right_inv := fun t => DFunLike.congr_fun hi.2 t
      map_add' := (inclusion hA N M).map_add }
  exact ⟨E, rfl, rfl, inclusion_tmul hA N M, reverse_tmul hA N hM⟩

end Components

section Naturality

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
  {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
  (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')
  (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M')

/-- Both original tensor-map squares commute on generators and hence on the quotient. -/
theorem naturality : Naturality hA hM hM' f g := by
  constructor
  · exact hom_ext A (fun _ _ => rfl)
  · apply hom_ext A
    intro n m
    obtain ⟨e, he⟩ := hM m
    have he' : (e : A) • g m = g m := by rw [← g.map_smul, he]
    change map A (f.restrictNondegeneratePart hA.op) g
        (reverse hA N hM (tmul A N M n m)) =
      reverse hA N' hM' (map A f g (tmul A N M n m))
    rw [reverse_tmul hA N hM n m e he, map_tmul, map_tmul,
      reverse_tmul hA N' hM' (f n) (g m) e he']
    congr 1
    exact Subtype.ext (f.map_smul (op (e : A)) n)

/-- The same prescribed equivalences satisfy both entire naturality squares. -/
theorem equivalenceNaturality : EquivalenceNaturality hA hM hM' f g := by
  obtain ⟨E, hE⟩ := prescribedEquivalence hA N hM
  obtain ⟨E', hE'⟩ := prescribedEquivalence hA N' hM'
  refine ⟨E, E', hE, hE', ?_, ?_⟩
  · rw [hE.1, hE'.1]
    exact (naturality hA hM hM' f g).1
  · rw [hE.2.1, hE'.2.1]
    exact (naturality hA hM hM' f g).2

end Naturality

/-- The entire unchanged five-universe additive tensor-smoothing family. -/
theorem tensorSmoothing :
    Langlands.Algebra.NonUnitalTensorSmoothingStatements.TensorSmoothing.{uA,uN,uM,uN',uM'} := by
  intro A _ hA N _ _ M _ _ hM
  refine ⟨inverseIdentities hA N hM, bijectivity hA N hM,
    prescribedEquivalence hA N hM, ?_⟩
  intro N' _ _ M' _ _ hM' f g
  exact ⟨naturality hA hM hM' f g, equivalenceNaturality hA hM hM' f g⟩

/-! Complete closed-target specializations at unequal universe assignments. -/

example : NonUnitalTensorSmoothingStatements.TensorSmoothing.{0,1,2,3,4} :=
  tensorSmoothing

example : NonUnitalTensorSmoothingStatements.TensorSmoothing.{4,3,2,1,0} :=
  tensorSmoothing

end Langlands.Algebra.NonUnitalTensorSmoothingProof
