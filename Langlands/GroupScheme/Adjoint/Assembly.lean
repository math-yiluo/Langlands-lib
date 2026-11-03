import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.Adjoint.QuotientDescent

/-! # Elementary assembly of actual adjoint quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The full all-test centre is a normal subgroup functor. -/
theorem center_isNormal (G : GroupScheme S) : (center G).IsNormal := by
  intro T g x _ hx
  have he : g * x * g⁻¹ = x := by
    rw [(commute_of_mem_center hx g).eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]
  exact hx

/-- The actual range of a full-centre representative is normal. -/
theorem IsSchemeTheoreticCenter.isNormal {z : H ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : (SubgroupFunctor.range z).IsNormal := by
  rw [hz.2]
  exact center_isNormal G

/-- In a separated group scheme with trivial full centre, the actual unit is a
closed representative of that centre. -/
theorem kernelUnit_isSchemeTheoreticCenter (G : GroupScheme S)
    [IsSeparated G.X.hom] (hc : center G = ⊥) :
    IsSchemeTheoreticCenter (kernelUnit G) := by
  refine ⟨?_, (range_kernelUnit G).trans hc.symm⟩
  exact kernelUnit_isClosedSubgroup G

/-- An explicit finite closed representative of a trivial full centre. -/
def finiteCenterOfCenterEqBot (G : GroupScheme S)
    [IsSeparated G.X.hom] (hc : center G = ⊥) :
    Σ Z : GroupScheme S,
      {z : Z ⟶ G // IsSchemeTheoreticCenter z ∧ IsFinite Z.X.hom} := by
  refine ⟨Grp.trivial (Over S), kernelUnit G,
    kernelUnit_isSchemeTheoreticCenter G hc, ?_⟩
  change IsFinite (𝟙 S)
  infer_instance

/-- A separated group scheme with trivial full centre has finite full centre. -/
theorem hasFiniteCenter_of_center_eq_bot (G : GroupScheme S)
    [IsSeparated G.X.hom] (hc : center G = ⊥) : HasFiniteCenter G := by
  let Z := finiteCenterOfCenterEqBot G hc
  exact ⟨Z.1, Z.2.1, Z.2.2⟩

/-- With separated target, a full-centre kernel range gives the closed actual
centre representative required by the quotient interface. -/
theorem isSchemeTheoreticCenter_kernelι_of_range_eq (q : G ⟶ H)
    [IsSeparated H.X.hom]
    (hker : SubgroupFunctor.range (kernelι q) = center G) :
    IsSchemeTheoreticCenter (kernelι q) :=
  ⟨(inferInstance : IsClosedImmersion (kernelι q).hom.hom.left), hker⟩

end General

section Field

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}

/-- Connected reductivity and triviality of the full centre imply adjointness. -/
theorem isAdjoint_of_isConnectedReductive_of_center_eq_bot
    (hG : IsConnectedReductive G) (hc : center G = ⊥) : IsAdjoint G := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact ⟨⟨hG, hasFiniteCenter_of_center_eq_bot G hc⟩, hc⟩

/-- The elementary final assembly only needs the quotient's structural properties,
its fppf conditions and equality of the actual kernel range with the full centre. -/
theorem isAdjointQuotient_of_fppf_kernel_range
    (q : G ⟶ A) (hG : IsConnectedReductive G)
    (hA : IsConnectedReductive A) (hc : center A = ⊥)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left)
    (hker : SubgroupFunctor.range (kernelι q) = center G) : IsAdjointQuotient q := by
  let : IsAffineHom A.X.hom := hA.isAffineHom
  exact isAdjointQuotient_of_fppf q hG
    (isAdjoint_of_isConnectedReductive_of_center_eq_bot hA hc)
    hflat hsurj hlfp (isSchemeTheoreticCenter_kernelι_of_range_eq q hker)

end Field

end Langlands.GroupScheme
