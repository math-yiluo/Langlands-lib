import Langlands.AbelianScheme.FieldFiniteKernelIsogenyStatement
import Langlands.AbelianScheme.FieldFiniteKernelQuasiFinite
import Langlands.AbelianScheme.FieldFiniteEndomorphismSurjectiveProof
import Langlands.AbelianScheme.FieldFiniteSurjectiveEndomorphismFlatProof
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite-kernel endomorphisms of abelian group schemes are isogenies -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite scheme-theoretic kernel makes an abelian endomorphism over any field
finite, flat and surjective. -/
theorem fieldFiniteKernelIsogeny :
    FieldFiniteKernelIsogenyStatement.{u} := by
  intro K _ G _ f hsm hp hconn hk
  let : IsProper G.X.hom := hp
  have : IsProper (f.hom.hom.left ≫ G.X.hom) := by
    simpa only [Over.w] using hp
  have : IsProper f.hom.hom.left := .of_comp _ G.X.hom
  have : LocallyQuasiFinite f.hom.hom.left :=
    fieldFiniteKernelQuasiFinite K G f hsm hp hconn hk
  have hfin : IsFinite f.hom.hom.left :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  have hsurj := fieldFiniteEndomorphismSurjective K G f hsm hp hconn hfin
  exact ⟨hfin,
    fieldFiniteSurjectiveEndomorphismFlat K G f hsm hp hconn hfin hsurj, hsurj⟩

end Langlands.GroupScheme
