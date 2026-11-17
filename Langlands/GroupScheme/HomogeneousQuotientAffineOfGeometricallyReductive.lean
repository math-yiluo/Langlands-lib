import Langlands.GroupScheme.HomogeneousQuotientPrincipalCover
import Langlands.GroupScheme.Reductive.InvariantUnitIdeal
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affineness of a supplied quotient under geometric reductivity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ J}
  (Q : HomogeneousQuotient i)

/-- A finite affine principal cover whose sections generate the unit ideal
in the section ring of the supplied quotient itself. -/
structure AffinePrincipalUnitCertificate where
  size : ℕ
  sections : Fin size → Γ(Q.scheme.left, ⊤)
  affine : ∀ j, IsAffineOpen (Q.scheme.left.basicOpen (sections j))
  span_eq_top : Ideal.span (Set.range sections) = ⊤

variable [IsAlgClosed k] [Smooth H.X.hom] [IsAffine H.X.left] [IsAffine J.X.left]

/-- Reflect an ambient coefficient certificate into the actual quotient
section ring through all-test invariant descent. -/
theorem span_eq_top_of_ambient_certificate
    (hH : IsGeometricallyReductive H) {I : Type} [Fintype I]
    (t : I → Γ(Q.scheme.left, ⊤)) (a : I → Γ(J.X.left, ⊤))
    (ha : ∑ j, a j * Q.projection.left.appTop (t j) = 1) :
    Ideal.span (Set.range t) = ⊤ := by
  have ha' : ∑ j, (Q.invariantSectionsEquiv (t j) : Γ(J.X.left, ⊤)) * a j = 1 := by
    change ∑ j, Q.projection.left.appTop (t j) * a j = 1
    calc
      _ = ∑ j, a j * Q.projection.left.appTop (t j) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 1 := ha
  have hs := InvariantPowerLift.span_eq_top_rightInvariantSubring i hH
    (fun j => Q.invariantSectionsEquiv (t j)) a ha'
  apply (Ideal.map_eq_top_of_bijective
    (f := Q.invariantSectionsEquiv.toRingHom) Q.invariantSectionsEquiv.bijective).mp
  rw [Ideal.map_span, ← Set.range_comp']
  exact hs

/-- Construct a finite affine principal unit certificate on the same supplied
quotient, assuming geometric reductivity of the subgroup. -/
def affinePrincipalUnitCertificate (hH : IsGeometricallyReductive H) :
    Q.AffinePrincipalUnitCertificate :=
  Classical.choice (by
    obtain ⟨n, t, a, ht, ha⟩ := Q.exists_finite_affine_principal_ambient_certificate hH
    exact ⟨⟨n, t, ht, Q.span_eq_top_of_ambient_certificate hH t a ha⟩⟩)

/-- A smooth affine geometrically reductive subgroup of an affine group has
an affine supplied homogeneous quotient over an algebraically closed field. -/
theorem isAffine_of_geometricallyReductive (hH : IsGeometricallyReductive H) :
    IsAffine Q.scheme.left := by
  let c := Q.affinePrincipalUnitCertificate hH
  apply isAffine_of_isAffineOpen_basicOpen (Set.range c.sections) c.span_eq_top
  rintro _ ⟨j, rfl⟩
  exact c.affine j

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient
