import Langlands.ClassFieldTheory.Local.Galois
import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Transfer

/-!
# Finite norm-residue relations on actual extensions

This module defines relations on candidate Artin maps and constructs quotient
and character transports from explicitly supplied maps and certificates.
It does not assert existence, uniqueness or normalization of reciprocity.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

variable (K : Type u) [Field K] [TopologicalSpace K]

/-- A family of candidate finite Artin homomorphisms on actual finite abelian
extensions. It carries no class-field assertion. -/
abbrev FiniteArtinFamily :=
  ∀ L : FiniteAbelianExtension K, Kˣ →ₜ* L.galoisGroup

variable {K}

/-- The finite norm-residue relation: a candidate map is onto the actual finite
Galois group and has exactly the actual field norm image as its kernel. -/
def FiniteNormResidueRelation (L : FiniteAbelianExtension K)
    (a : Kˣ →ₜ* L.galoisGroup) : Prop :=
  a.toMonoidHom.ker = normSubgroup K L.field ∧ Function.Surjective a

/-- Compatibility of candidate finite maps with restriction along actual
inclusions of finite abelian intermediate extensions. -/
def FiniteArtinRestrictionRelation (a : FiniteArtinFamily K) : Prop :=
  ∀ (L M : FiniteAbelianExtension K) (h : L.field ≤ M.field),
    (L.restrictionOfLE M h).comp (a M) = a L

/-- The unnormalized finite-system relation. Normalization and any existence
or uniqueness assertion are deliberately separate. -/
def FiniteArtinSystemRelation (a : FiniteArtinFamily K) : Prop :=
  (∀ L, FiniteNormResidueRelation L (a L)) ∧ FiniteArtinRestrictionRelation a

/-- A candidate map to the actual absolute-Galois abelianization gives an
actual family by finite restriction. No choice of such a candidate is made. -/
def finiteFamilyOfHom (a : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K) :
    FiniteArtinFamily K :=
  fun L => L.abelianRestriction.comp a

/-- The finite norm-residue and density conditions on a candidate profinite
reciprocity homomorphism. This relation contains no normalization. -/
def ProfiniteNormResidueRelation
    (a : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K) : Prop :=
  DenseRange a ∧ FiniteArtinSystemRelation (finiteFamilyOfHom a)

variable [IsTopologicalRing K]

/-- A map killing the actual norm image descends continuously to the actual
norm quotient. The well-definedness certificate is supplied explicitly. -/
def finiteNormQuotientMap (L : FiniteAbelianExtension K)
    (a : Kˣ →ₜ* L.galoisGroup)
    (h : normSubgroup K L.field ≤ a.toMonoidHom.ker) :
    NormQuotient K L.field →ₜ* L.galoisGroup where
  toMonoidHom := QuotientGroup.lift _ a.toMonoidHom h
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr a.continuous

/-- A certified candidate finite norm-residue map induces a continuous
isomorphism of its actual norm quotient. This is conditional on the map
and its certificate, not a canonical Artin map constructor. -/
def finiteNormResidueEquiv (L : FiniteAbelianExtension K)
    (a : Kˣ →ₜ* L.galoisGroup) (h : FiniteNormResidueRelation L a) :
    NormQuotient K L.field ≃ₜ* L.galoisGroup := by
  let e := (QuotientGroup.quotientMulEquivOfEq h.1.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective a.toMonoidHom h.2)
  refine { e with
    continuous_toFun := ?_
    continuous_invFun := continuous_of_discreteTopology }
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  change Continuous (fun x : Kˣ => a x)
  exact a.continuous

/-- Continuous complex characters trivial on the actual field norm image. -/
def NormTrivialCharacter (L : FiniteAbelianExtension K) :=
  {χ : Kˣ →ₜ* ℂˣ // normSubgroup K L.field ≤ χ.toMonoidHom.ker}

/-- The genuine quotient universal property for norm-trivial characters.
This descent uses no Artin homomorphism or class-field-theoretic assertion. -/
def normQuotientCharacterEquiv (L : FiniteAbelianExtension K) :
    NormTrivialCharacter L ≃ (NormQuotient K L.field →ₜ* ℂˣ) where
  toFun χ :=
    { toMonoidHom := QuotientGroup.lift _ χ.1.toMonoidHom χ.2
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr χ.1.continuous }
  invFun χ :=
    ⟨χ.comp
      { toMonoidHom := normQuotientProjection K L.field
        continuous_toFun := QuotientGroup.continuous_mk },
      by
        intro x hx
        change χ (QuotientGroup.mk x) = 1
        rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]⟩
  left_inv χ := by
    apply Subtype.ext
    ext x
    rfl
  right_inv χ := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro g
    rfl

section CharacterTransport

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Transport continuous complex quasicharacters by a genuine continuous
group isomorphism. Both directions use the given isomorphism. -/
def characterTransport (e : G ≃ₜ* H) : (G →ₜ* ℂˣ) ≃ (H →ₜ* ℂˣ) where
  toFun χ := χ.comp (e.symm : H →ₜ* G)
  invFun χ := χ.comp (e : G →ₜ* H)
  left_inv χ := by ext x; simp
  right_inv χ := by ext x; simp

end CharacterTransport

/-- Character transport attached to an explicitly certified finite candidate.
The resulting characters on `Kˣ` are exactly those trivial on its norm group. -/
def finiteArtinCharacterEquiv (L : FiniteAbelianExtension K)
    (a : Kˣ →ₜ* L.galoisGroup) (h : FiniteNormResidueRelation L a) :
    (L.galoisGroup →ₜ* ℂˣ) ≃ NormTrivialCharacter L :=
  (characterTransport (finiteNormResidueEquiv L a h).symm).trans
    (normQuotientCharacterEquiv L).symm

end Langlands.LocalClassField

namespace Langlands.LocalClassField

universe u v

section FiniteTransfer

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Finite G] [DiscreteTopology G] (H : Subgroup G)

/-- Mathlib's actual transfer into the closed-commutator quotient of a subgroup
of a finite discrete group. Continuity follows from the source topology. -/
def finiteTransfer : G →ₜ* TopologicalAbelianization H where
  toMonoidHom := MonoidHom.transfer (abelianizationProjection H).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The finite transfer descended to the source's actual abelianization. -/
def finiteAbelianTransfer :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization H := by
  letI := abelianizationHausdorff H
  exact abelianizationLift (finiteTransfer H)

end FiniteTransfer

section FiniteTower

variable {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] (E : IntermediateField K M)

/-- The actual fixing subgroup is continuously isomorphic to `Gal(M/E)`.
Both topologies are their inherited finite discrete Krull topologies. -/
def finiteFixingGroupEquiv : E.fixingSubgroup ≃ₜ* Gal(M/E) where
  toMulEquiv := IntermediateField.fixingSubgroupEquiv E
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Inclusion of the actual Galois group over the intermediate field into
the Galois group over the base field. -/
def finiteGaloisInclusion : Gal(M/E) →ₜ* Gal(M/K) :=
  ({ toMonoidHom := E.fixingSubgroup.subtype
     continuous_toFun := continuous_subtype_val } :
      E.fixingSubgroup →ₜ* Gal(M/K)).comp
    (finiteFixingGroupEquiv E).symm

/-- The induced inclusion on actual abelianized finite Galois groups,
in the direction corresponding to the field norm. -/
def finiteGaloisAbelianInclusion :
    TopologicalAbelianization Gal(M/E) →ₜ* TopologicalAbelianization Gal(M/K) :=
  abelianizationMap (finiteGaloisInclusion E)

/-- Finite group transfer in the opposite direction, expressed using the
actual automorphism groups rather than an unidentified abstract subgroup. -/
def finiteGaloisAbelianTransfer :
    TopologicalAbelianization Gal(M/K) →ₜ* TopologicalAbelianization Gal(M/E) :=
  (abelianizationMap (finiteFixingGroupEquiv E :
    E.fixingSubgroup →ₜ* Gal(M/E))).comp (finiteAbelianTransfer E.fixingSubgroup)

/-- The finite norm compatibility square for specified candidate maps.
This is a relation, not a proof that candidate maps are reciprocity maps. -/
def FiniteNormCompatibility
    (aK : Kˣ →* TopologicalAbelianization Gal(M/K))
    (aE : Eˣ →* TopologicalAbelianization Gal(M/E)) : Prop :=
  aK.comp (normUnits K E) =
    (finiteGaloisAbelianInclusion E).toMonoidHom.comp aE

/-- The finite field-inclusion/transfer square for specified candidate maps.
Field inclusion goes from `Kˣ` to `Eˣ`; transfer goes from the abelianized
group over `K` to the abelianized group over `E`. -/
def FiniteTransferCompatibility
    (aK : Kˣ →* TopologicalAbelianization Gal(M/K))
    (aE : Eˣ →* TopologicalAbelianization Gal(M/E)) : Prop :=
  aE.comp (Units.map (algebraMap K E).toMonoidHom) =
    (finiteGaloisAbelianTransfer E).toMonoidHom.comp aK

end FiniteTower

end Langlands.LocalClassField
