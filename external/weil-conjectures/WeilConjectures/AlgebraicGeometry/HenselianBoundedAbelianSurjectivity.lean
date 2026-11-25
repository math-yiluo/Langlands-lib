/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion
import WeilConjectures.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep

/-!
# Surjectivity of henselian restriction for bounded abelian coefficients

Source: Stacks Project, Tags 09ZE, 09ZH and 09ZI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Henselian restriction is surjective for abelian sheaves killed by one positive
integer. This supplies only the bounded, abelian, surjective part of comparison;
it is independent of the general-coefficient effacement theorem in Gabber.lean.

Source: Stacks Project, Tags 09ZE (finite-coefficient effacement), 09ZH (degree zero)
and 09ZI (the long-exact-sequence induction).
(blueprint: lem-weil-pbc-henselian-bounded-abelian-surjectivity)

Proof: Regard G as a sheaf of modules over the finite ring Z/n. To prove comparison
in all degrees for these sheaves, first use 09ZE within Z/n-module sheaves. Here
03SA(3), inverse-image preservation of colimits and 03Q5 represent a closed-fibre
class by a constructible Z/n-module sheaf C mapping to G. Apply 09Z7(3) to embed
C in a finite sum of finite pushforwards of finite constant Z/n-modules. Finite
base change 0959 and finite-pushforward cohomology 03QP identify each summand's
class with one on the closed fibre of its finite cover. Tag 09ZD supplies a finite
surjective cover killing that finite constant class. Push forward the unit along
that cover. It is monic by surjectivity on geometric points, and the edge/unit
compatibility identifies its cohomological effect with the pullback just killed.
Take the finite sum of these monomorphisms and compose with the embedding of C.
Push out along C → G. This yields a monomorphism G → G' killing the original
class; G' and its cokernel remain Z/n-module sheaves. All maps here are Z/n-linear.
The same construction with the closed subscheme equal to the whole affine scheme
kills classes on X. Induct on q, simultaneously proving bijectivity for every
Z/n-module sheaf. In degree zero, henselian Stein connectedness gives the
nonempty connected closed-fibre intersections for every finite cover; apply the
abelian global-sections criterion and the degree-zero cohomology comparison.
For injectivity in degree q, efface
a source class, express it as a boundary from the cokernel, and use bijectivity
in degree q-1 and exactness to show that a class with zero restriction was zero.
For surjectivity, efface a closed-fibre class, express it as a boundary from the
cokernel on the fibre, lift that class by degree q-1 surjectivity, and take its
boundary on X. Naturality of the long exact sequence gives the required image.
Finally retain just surjectivity and forget the finite-ring module structure.
Neither the general Λ-module effacement nor the comparison declaration in
Gabber.lean is used. Lift Z/n to the coefficient universe when realizing the
argument in ModuleCat. The cases n = 1, q = 0 and empty spectra are included. -/
theorem surjective_cohomologyMap_of_henselianRing_of_nsmul_eq_zero
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hG : n • 𝟙 G = 0) (q : ℕ) :
    Function.Surjective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G q) := by
  have hzero (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G 0) := by
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    have : IsClosedImmersion i :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hi : Set.range i = PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G) := by
      apply isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections i
      intro X' p hp C hC hC'
      rw [hi]
      exact (p.spectralSpace_and_isClosed_and_isConnected_inter I).2.2 C hC hC'
    let a := fun g : (Sheaf.Γ _ AddCommGrpCat.{u + 1}).obj G ↦
      (Sheaf.H.equiv₀ G terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g)
    let G₀ := (i)^*[AddCommGrpCat.{u + 1}].obj G
    let b := fun g : (Sheaf.Γ (Spec (.of (A ⧸ I))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj G₀ ↦
      (Sheaf.H.equiv₀ G₀ terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
          terminalIsTerminal).hom.app G₀ g)
    have ha : Function.Bijective a :=
      (Sheaf.H.equiv₀ G terminalIsTerminal).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso
          ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G))
    have hb : Function.Bijective b :=
      (Sheaf.H.equiv₀ G₀ terminalIsTerminal).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso
          ((Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
            terminalIsTerminal).hom.app G₀))
    have hres := ConcreteCategory.bijective_of_isIso
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G)
    have hab : ∀ g, cohomologyMap i G 0 (a g) =
        b (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G g) :=
      cohomologyMap_zero_eq_globalSectionsUpperStarMap i G
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := ha.2 x
      obtain ⟨y, rfl⟩ := ha.2 y
      apply congrArg a
      apply hres.1
      apply hb.1
      change cohomologyMap i G 0 (a x) = cohomologyMap i G 0 (a y) at hxy
      rw [hab, hab] at hxy
      exact hxy
    · intro y
      obtain ⟨y, rfl⟩ := hb.2 y
      obtain ⟨x, rfl⟩ := hres.2 y
      exact ⟨a x, hab x⟩
  have hcomparison : ∀ (q : ℕ)
      (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      n • 𝟙 G = 0 → Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G q) := by
    intro q
    induction q with
    | zero => exact fun G _ ↦ hzero G
    | succ q ih =>
      exact fun G hG ↦
        bijective_cohomologyMap_succ_of_henselianRing_of_nsmul_eq_zero I n hn q ih G hG
  exact (hcomparison q G hG).2

end AlgebraicGeometry.Etale
