import Langlands.Algebra.NonUnitalTensorSmoothing

/-!
# Prescribed additive tensor smoothing and naturality

Statement interfaces for the additive isomorphism in Renard (9 July 2026),
I.4.3, printed p. 25 / PDF p. 31, over the published original-action tensor,
nondegenerate-part subtype, inclusion and balanced reverse.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalTensorSmoothingStatements

open NonUnitalModuleTensor NonUnitalTensorSmoothing

universe uA uN uM uN' uM'

section Components

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hM : IsNondegenerate A M)

/-- Both inverse identities concern the entire prescribed additive maps. -/
def InverseIdentities : Prop :=
  (reverse hA N hM).comp (inclusion hA N M) =
      AddMonoidHom.id (Tensor A (nondegeneratePart hA.op N) M) ∧
    (inclusion hA N M).comp (reverse hA N hM) =
      AddMonoidHom.id (Tensor A N M)

/-- Both prescribed maps are bijective, without nondegeneracy of the original `N`. -/
def Bijectivity : Prop :=
  Function.Bijective (inclusion hA N M) ∧ Function.Bijective (reverse hA N hM)

/-- Whole-map pins and pure-tensor formulas, using every fixing idempotent. -/
def EquivalenceData
    (E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M) : Prop :=
  E.toAddMonoidHom = inclusion hA N M ∧
    E.symm.toAddMonoidHom = reverse hA N hM ∧
    (∀ (n : nondegeneratePart hA.op N) (m : M),
      E (tmul A (nondegeneratePart hA.op N) M n m) = tmul A N M (n : N) m) ∧
    (∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
      E.symm (tmul A N M n m) =
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m)

/-- Existence of the equivalence with both entire maps prescribed is a conclusion. -/
def PrescribedEquivalence : Prop :=
  ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
    EquivalenceData hA N hM E

end Components

section Naturality

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N' : Type uN'} [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
  {M' : Type uM'} [AddCommGroup M'] [NonUnitalModule A M']
  (hM : IsNondegenerate A M) (hM' : IsNondegenerate A M')

/-- Both whole-map squares use the actual original intertwiners and their restriction. -/
def Naturality (f : NonUnitalModuleHom Aᵐᵒᵖ N N')
    (g : NonUnitalModuleHom A M M') : Prop :=
  (map A f g).comp (inclusion hA N M) =
      (inclusion hA N' M').comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
    (map A (f.restrictNondegeneratePart hA.op) g).comp (reverse hA N hM) =
      (reverse hA N' hM').comp (map A f g)

/-- Prescribed equivalences at both pairs satisfy both entire additive-map squares. -/
def EquivalenceNaturality (f : NonUnitalModuleHom Aᵐᵒᵖ N N')
    (g : NonUnitalModuleHom A M M') : Prop :=
  ∃ E : Tensor A (nondegeneratePart hA.op N) M ≃+ Tensor A N M,
    ∃ E' : Tensor A (nondegeneratePart hA.op N') M' ≃+ Tensor A N' M',
      EquivalenceData hA N hM E ∧ EquivalenceData hA N' hM' E' ∧
        (map A f g).comp E.toAddMonoidHom =
          E'.toAddMonoidHom.comp (map A (f.restrictNondegeneratePart hA.op) g) ∧
        (map A (f.restrictNondegeneratePart hA.op) g).comp E.symm.toAddMonoidHom =
          E'.symm.toAddMonoidHom.comp (map A f g)

end Naturality

/-- Closed additive statement family, with five independent universe parameters. -/
def TensorSmoothing : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M),
    InverseIdentities hA N hM ∧ Bijectivity hA N hM ∧ PrescribedEquivalence hA N hM ∧
      ∀ (N' : Type uN') [AddCommGroup N'] [NonUnitalModule Aᵐᵒᵖ N']
        (M' : Type uM') [AddCommGroup M'] [NonUnitalModule A M']
        (hM' : IsNondegenerate A M')
        (f : NonUnitalModuleHom Aᵐᵒᵖ N N') (g : NonUnitalModuleHom A M M'),
        Naturality hA hM hM' f g ∧ EquivalenceNaturality hA hM hM' f g

end Langlands.Algebra.NonUnitalTensorSmoothingStatements
