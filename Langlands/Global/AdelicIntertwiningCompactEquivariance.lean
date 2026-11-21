import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicIntertwiningOperator
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Whittaker.Algebraic

/-! # Compact equivariance of the adelic intertwining operator -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- The restriction of right translation on scalar functions to an infinite adelic subgroup. -/
def functionInfiniteSubgroupAction (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) :
    Representation ℂ Kinf (AdelicGroupPoints F G → ℂ) :=
  (Whittaker.rightTranslation ℂ (AdelicGroupPoints F G)).comp
    ((AdelicGroupPoints.ofInfinite F G).toMonoidHom.comp Kinf.subtype)

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.FiniteVectors

variable {F : Type u} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
  (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (c : M' ⟶ M) (π' : Q ⟶ M')
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (lam : ComplexCharacterParameter F P)

local notation "μ" => intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)
local notation "I" => hK.intertwiningIntegrand iU (iV ≫ q) w
local notation "T[" f "]" => hK.intertwiningOperator hQ iU l iV c π' w f lam
local notation "R" => functionInfiniteSubgroupAction F G (Subgroup.comap
  (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K)

omit [LocallyOfFiniteType G.X.hom] [IsAffine Q.X.left] [IsAffine V.X.left]
  [IsClosedImmersion q.hom.hom.left] [IsClosedImmersion (iV ≫ q).hom.hom.left] in
private theorem intertwiningIntegrand_rightTranslate
    (f : AdelicGroupPoints F G → ℂ) {k : AdelicGroupPoints F G} (hk : k ∈ K)
    (g : AdelicGroupPoints F G) (x : LeftCosetSpace
      (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w))) :
    I (fun y => f (y * k)) lam g x = I f lam (g * k) x := by
  unfold IsIwasawaCompact.intertwiningIntegrand IsIwasawaCompact.parameterTwist
    IsIwasawaCompact.heightPower
  rw [← mul_assoc _ g k, hK.height_mul_right _ hk]

/-- The untwisted operator commutes with right translation by the common Iwasawa compact. -/
theorem IsIwasawaCompact.intertwiningOperator_rightTranslate
    (f : AdelicGroupPoints F G → ℂ) {k : AdelicGroupPoints F G} (hk : k ∈ K)
    (g : AdelicGroupPoints F G) :
    T[fun y => f (y * k)] g = T[f] (g * k) := by
  unfold IsIwasawaCompact.intertwiningOperator IsIwasawaCompact.intertwiningIntegral
    IsIwasawaCompact.heightPower
  rw [hQ.height_mul_right g hk]
  exact congrArg (_ * ·) (integral_congr_ae (Filter.Eventually.of_forall
    (intertwiningIntegrand_rightTranslate hK iU iV w lam f hk g)))

omit [IsAffine Q.X.left] [IsClosedImmersion q.hom.hom.left] in
private theorem integrable_intertwiningIntegrand_of_mem_orbitSpan
    {φ f : AdelicGroupPoints F G → ℂ}
    (hφ : ∀ g, Integrable (I φ lam g) μ) (hf : f ∈ orbitSpan R φ) :
    ∀ g, Integrable (I f lam g) μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    intro g
    convert hφ (g * ofInfinite F G k.val) using 1
    funext x
    exact intertwiningIntegrand_rightTranslate hK iU iV w lam φ k.property g x
  | zero =>
    intro g
    convert integrable_zero _ ℂ μ using 1
    funext x
    simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
      Pi.zero_apply, zero_mul]
  | add f f' _ _ hf hf' =>
    intro g
    convert (hf g).add (hf' g) using 1
    funext x
    simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
      Pi.add_apply, add_mul]
  | smul a f _ hf =>
    intro g
    convert (hf g).const_mul a using 1
    funext x
    simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
      Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- On the source vector's infinite compact orbit span, the integral gives a linear
intertwiner with the same compact source at each parameter where the integral converges. -/
def IsIwasawaCompact.intertwiningCompactMap (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ g, Integrable (I φ lam g) μ) :
    (orbitSubrepresentation R φ).toRepresentation.IntertwiningMap R where
  toLinearMap :=
    { toFun := fun f => T[f.val]
      map_add' f f' := by
        funext g
        change T[f.val + f'.val] g = T[f.val] g + T[f'.val] g
        unfold IsIwasawaCompact.intertwiningOperator IsIwasawaCompact.intertwiningIntegral
        have heq : I (f.val + f'.val) lam g = I f.val lam g + I f'.val lam g := by
          funext x
          simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
            Pi.add_apply, add_mul]
        simp only [heq, Pi.add_apply, integral_add
          (integrable_intertwiningIntegrand_of_mem_orbitSpan hK iU iV w lam hφ f.property g)
          (integrable_intertwiningIntegrand_of_mem_orbitSpan hK iU iV w lam hφ f'.property g),
          mul_add]
      map_smul' a f := by
        funext g
        change T[a • f.val] g = a * T[f.val] g
        unfold IsIwasawaCompact.intertwiningOperator IsIwasawaCompact.intertwiningIntegral
        have heq : I (a • f.val) lam g = fun x => a * I f.val lam g x := by
          funext x
          simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
            Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [heq, integral_const_mul, mul_left_comm] }
  isIntertwining' k := by
    ext f g
    exact hK.intertwiningOperator_rightTranslate hQ iU l iV c π' w lam f.val k.property g

/-- The compact intertwiner sends the original orbit vector to the intertwining value. -/
theorem IsIwasawaCompact.intertwiningCompactMap_apply
    (φ : AdelicGroupPoints F G → ℂ) (hφ : ∀ g, Integrable (I φ lam g) μ) :
    hK.intertwiningCompactMap hQ iU l iV c π' w lam φ hφ
      ⟨φ, self_mem_orbitSpan R φ⟩ = T[φ] :=
  rfl

/-- Compact finiteness of the inducing vector passes to the intertwining value. -/
theorem IsIwasawaCompact.intertwiningOperator_isInfiniteSubgroupFinite
    (φ : AdelicGroupPoints F G → ℂ) (hint : ∀ g, Integrable (I φ lam g) μ)
    (hφ : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ) :
    IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) T[φ] := by
  let : Module.Finite ℂ (orbitSubrepresentation R φ).toSubmodule := hφ
  have horig : IsFiniteVector (orbitSubrepresentation R φ).toRepresentation
      (⟨φ, self_mem_orbitSpan R φ⟩ : (orbitSubrepresentation R φ).toSubmodule) :=
    Submodule.finiteDimensional_of_le le_top
  exact horig.map (hK.intertwiningCompactMap hQ iU l iV c π' w lam φ hint)

/-- A finite adelic subgroup contained in the compact fixes the output whenever it fixes the input. -/
theorem IsIwasawaCompact.intertwiningOperator_fixedByFiniteLevel
    (L : Subgroup (FiniteAdelicGroupPoints F G))
    (hle : L ≤ K.comap (ofFinite F G).toMonoidHom) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : ∀ b ∈ L, ∀ g, φ (g * ofFinite F G b) = φ g) :
    ∀ b ∈ L, ∀ g, T[φ] (g * ofFinite F G b) = T[φ] g := by
  intro b hb g
  have hk : ofFinite F G b ∈ K := hle hb
  calc
    T[φ] (g * ofFinite F G b) = T[fun y => φ (y * ofFinite F G b)] g :=
      (hK.intertwiningOperator_rightTranslate hQ iU l iV c π' w lam φ hk g).symm
    _ = T[φ] g := congrArg (fun f => T[f] g) (funext (hφ b hb))

end Langlands.Global.AdelicGroupPoints
