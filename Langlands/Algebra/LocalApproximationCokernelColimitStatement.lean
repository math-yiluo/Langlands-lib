import Langlands.Algebra.LocalApproximationCokernel

/-! # Colimit preservation by actual cokernels of compatible local module maps -/

namespace Langlands.Algebra

/-- For a compatible map `φ : CompatibleMap E F f` of local module systems over one local
algebra system `D`, if the additive colimit comparison of `E` is surjective and that of `F` is
bijective, then the additive colimit comparison of the actual range-quotient system
`φ.cokernelSystem`, with target `N ⧸ LinearMap.range f`, is bijective. All nine universes are
independent. This internal claim supports the last paragraph of the proof of Stacks 046Y; this
definition states the proposition. -/
def LocalCokernelColimitPreservationStatement.{uI, uA, uB, uE, uF, uR, uS, uM, uN} : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (φ : LocalModuleSystem.CompatibleMap E F f),
    Function.Surjective E.moduleColimitMap → Function.Bijective F.moduleColimitMap →
      Function.Bijective φ.cokernelSystem.moduleColimitMap

end Langlands.Algebra
