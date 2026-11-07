import Langlands.Global.Arithmetic.HarrisProposition48Statement
import Langlands.Global.CompletionPadicTower
import Langlands.Weil.Local.ExtensionWeil
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.Automorphic.AssociatedFactorStatement

/-!
# Henniart's global construction: the relative Weil image contains `R_E`

Henniart (2000), Théorème 3.1, page 448, in the relative form of the Library's
witnessed pairs: for a p-adic field `K` and a homomorphism `q` from its absolute
Galois group to a finite group, there are a Galois extension `E/F` of number
fields, a finite place `v` of `F` and an isomorphism `K ≅ F_v` such that, after
transport along this isomorphism, the Weil image of the witnessed relative pairs
at `v` contains every unitary virtual class of `W_K` factoring through `q`.
`HenniartGlobalizationStatement` takes Harris (1998), Proposition 4.8 as its only
hypothesis. Proposition definitions only.
-/

noncomputable section

universe u uK uQ uW uP

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.ClassField.Global

section Transport

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p)

/-- Prime transport of the canonical completion package leaves the actual local
Weil group unchanged. -/
def padicFieldAtWeilEquiv :
    localWeilGroup (padicFieldAt v h) ≃ₜ* localWeilGroup (padicField v) := by
  subst h
  exact ContinuousMulEquiv.refl _

/-- The local Weil map `W_K → W_{F_v}` of a `ℚ_p`-algebra isomorphism
`K ≅ F_v`: the map of `extensionWeilMap` along the inverse embedding
`F_v → K`, followed by prime transport. -/
def completionWeilTransport (K : PadicField.{uK} p)
    (f : letI := (padicFieldAt v h).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier) :
    localWeilGroup K →ₜ* localWeilGroup (padicField v) :=
  letI := (padicFieldAt v h).algebra
  (padicFieldAtWeilEquiv v h : localWeilGroup (padicFieldAt v h) →ₜ*
      localWeilGroup (padicField v)).comp
    (extensionWeilMap (padicFieldAt v h) K f.symm.toAlgHom)

end Transport

/-- Henniart (2000), Théorème 3.1, relative form. For every arithmetic
fundamental-class family `c`, every p-adic field `K` and every homomorphism `q`
from the absolute Galois group of `K` to a finite group, there are a finite
Galois extension `E/F` of number fields, a finite place `v` of `F` above `p` and
a `ℚ_p`-algebra isomorphism `f : K ≅ F_v` such that every unitary virtual class
`x` of `W_K` whose irreducible constituents factor through `q` is the restriction
along `completionWeilTransport v h K f` of an element `y` of the Weil image
`weilImage F E c v` of the witnessed relative pairs at `v`. The comparison takes
place in the exact Grothendieck group of continuous representations of `W_K`. -/
def RelativeGaloisGlobalization : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{0}, RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q),
    ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E)
      (_ : Algebra F E) (_ : IsGalois F E)
      (v : FinitePlace F) (h : residuePrime v = p)
      (f : letI := (padicFieldAt v h).algebra
        K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
      ∀ [CompactSpace (AdeleQuotient F)],
      ∀ x ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW} K q,
        ∃ y ∈ weilImage.{0, uW, uP} F E c v,
          ExactGrothendieckGroup.continuousRestrict (completionWeilTransport v h K f)
              (LocalWeil.realizeExact (padicField v)
                (LocalWeil.includeUnitary (padicField v) y)) =
            LocalWeil.realizeExact K (LocalWeil.includeUnitary K x)

/-- Henniart (2000), Sections 3.3–3.7: Harris (1998), Proposition 4.8 implies
the relative form of Théorème 3.1. Harris's proposition is the only hypothesis. -/
def HenniartGlobalizationStatement : Prop :=
  Harris.Proposition48Statement.{uK, 0, 0, 0, uP} →
    RelativeGaloisGlobalization.{uK, uQ, uW, uP}

end Langlands.Global
