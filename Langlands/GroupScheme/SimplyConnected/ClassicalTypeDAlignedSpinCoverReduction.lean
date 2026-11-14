import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverStatement
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotientStatement
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeightTransport
import Langlands.GroupScheme.Quaternionic.EvenSpecialOrthogonalFormStatement
import Langlands.GroupScheme.CentralIsogeny.Transport

/-!
# Reduction of aligned type-`D` spin covers to the vector quotient and Tits's forms

`classicalTypeDAlignedSpinCover_of_vectorQuotient` derives
`ClassicalTypeDAlignedSpinCoverStatement` from `TypeDVectorQuotientStatement` and
`Quaternionic.EvenSpecialOrthogonalFormStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Reduction.** The vector quotient of a simply connected group of type `D_n` is a
form of `SO_{2n}`, and Tits's realization of such forms identifies it with `O(q)⁰`; the
composite `G ⟶ O(q)⁰ ⟶ O(q)` is an aligned spin cover. -/
theorem classicalTypeDAlignedSpinCover_of_vectorQuotient
    (hquot : TypeDVectorQuotientStatement.{u})
    (hforms : Quaternionic.EvenSpecialOrthogonalFormStatement.{u}) :
    ClassicalTypeDAlignedSpinCoverStatement.{u} := by
  intro K _ G _ _ d n e hn hsc habs hcartan hstar
  obtain ⟨H, _, _, p, hp, hH, halign⟩ := hquot K G d n e hn hsc habs hcartan
    (fun g a ha => hstar g a (by omega))
  obtain ⟨D, _, _, _, _, degree, m, hdeg, hdim, hm, τ, hτ, q, hq, hsm, ⟨φ⟩⟩ :=
    hforms K H n hn hH
  have := hsm
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, degree, m, hdeg, hdim,
    hm, τ, hτ, q, hq, p ≫ φ.hom ≫ identityComponentι (τ.isometryGroup q),
    ⟨hsc, hsm, p ≫ φ.hom, hp.comp_iso φ, by rw [Category.assoc]⟩, ?_⟩
  intro v hv
  simpa only [Category.assoc] using ((halign v hv).comp_iso φ).comp_identityComponentι

end Langlands.GroupScheme
