import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.CuspidalSupport.GroupTransport

/-!
# Canonical Jacquet lift transport through continuous group equivalences

These derived proposition definitions express naturality of the existing compact
average, stable image and actual restricted Jacquet quotient maps. They do not
prove the transport assertions or assume either canonical-lift conclusion.
-/

namespace Langlands.Jacquet

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Normalized averaging is unchanged on the same carrier under group transport. -/
def CanonicalLiftAverageGroupTransportClause : Prop :=
  ∀ (e : H ≃ₜ* G) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)),
    K.toSubgroup.map e.toMonoidHom = L.toSubgroup →
      Compact.averageMap (ρ.comp e.toMonoidHom)
        (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK =
      Compact.averageMap ρ hρ L hL

/-- Membership of the same ambient vector in the actual all-power stable images
is equivalent, using its two corresponding fixed-vector subtypes. -/
def CanonicalLiftStableImageGroupTransportClause : Prop :=
  ∀ (e : H ≃ₜ* G) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)),
    K.toSubgroup.map e.toMonoidHom = L.toSubgroup →
      ∀ (g : H) (v : V)
        (hvK : v ∈ fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup)
        (hvL : v ∈ fixedVectors ρ L.toSubgroup),
        (⟨v, hvK⟩ ∈ stableImage (ρ.comp e.toMonoidHom)
          (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g) ↔
        (⟨v, hvL⟩ ∈ stableImage ρ hρ L hL (e g))

/-- The canonical-lift kernel equality holds for the pulled-back data exactly
when it holds for the target data, at the actual image subgroups. -/
def CanonicalLiftPowerKernelGroupTransportClause : Prop :=
  ∀ (e : H ≃ₜ* G) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)),
    K.toSubgroup.map e.toMonoidHom = L.toSubgroup →
      ∀ (g : H) (N M : Subgroup H) (N' M' : Subgroup G)
        (hMN : M ≤ Subgroup.normalizer N) (hM'N' : M' ≤ Subgroup.normalizer N'),
        N.map e.toMonoidHom = N' → M.map e.toMonoidHom = M' →
          ((powerKernelSup (ρ.comp e.toMonoidHom)
            (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g =
              LinearMap.ker (fixedJacquetMap (ρ.comp e.toMonoidHom)
                N M hMN K.toSubgroup)) ↔
          (powerKernelSup ρ hρ L hL (e g) =
              LinearMap.ker (fixedJacquetMap ρ N' M' hM'N' L.toSubgroup)))

/-- Bijectivity of the actual stable-image Jacquet quotient map is invariant
under group transport, with the existing unnormalized fixed-quotient codomains. -/
def CanonicalLiftBijectiveGroupTransportClause : Prop :=
  ∀ (e : H ≃ₜ* G) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)),
    K.toSubgroup.map e.toMonoidHom = L.toSubgroup →
      ∀ (g : H) (N M : Subgroup H) (N' M' : Subgroup G)
        (hMN : M ≤ Subgroup.normalizer N) (hM'N' : M' ≤ Subgroup.normalizer N'),
        N.map e.toMonoidHom = N' → M.map e.toMonoidHom = M' →
          (Function.Bijective (stableImageJacquetMap (ρ.comp e.toMonoidHom)
            (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g N M hMN) ↔
          Function.Bijective (stableImageJacquetMap ρ hρ L hL (e g) N' M' hM'N'))

/-- Group-equivalence naturality of normalized averaging, stable-image
membership, canonical-lift kernel identification and actual quotient bijectivity. -/
def CanonicalLiftGroupTransportStatement : Prop :=
  CanonicalLiftAverageGroupTransportClause (G := G) (H := H) (V := V) ∧
  CanonicalLiftStableImageGroupTransportClause (G := G) (H := H) (V := V) ∧
  CanonicalLiftPowerKernelGroupTransportClause (G := G) (H := H) (V := V) ∧
  CanonicalLiftBijectiveGroupTransportClause (G := G) (H := H) (V := V)

end Langlands.Jacquet
