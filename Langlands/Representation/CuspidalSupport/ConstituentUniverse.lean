import Langlands.Representation.CuspidalSupport.ConstituentProof
import Langlands.Representation.Category.UniverseLift

/-! Actual cuspidal constituent maps between independently sized carriers. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The existing constituent theorem transported through actual carrier lifts.
The occurrence hypothesis is a surjective map from an invariant subspace. -/
theorem leviCuspidalConstituent_maps :
    letI := T.topology
    ∀ (A : Rep.{uV} ℂ (B.Levi F.Carrier))
      (D : Rep.{uW} ℂ (B.Levi F.Carrier)),
      IsAdmissible A.ρ → Representation.IsIrreducible D.ρ →
      IsLeviCuspidal B D.ρ →
      (∃ S : Subrepresentation A.ρ,
        ∃ q : S.toRepresentation.IntertwiningMap D.ρ, Function.Surjective q) →
      (∃ i : D.ρ.IntertwiningMap A.ρ, Function.Injective i) ∧
      (∃ q : A.ρ.IntertwiningMap D.ρ, Function.Surjective q) := by
  let := T.topology
  intro A D hAa hDi hDc hDA
  let As := SmoothRep.of A.ρ hAa.1
  let Ds := SmoothRep.of D.ρ hDc.1.1
  let A' := SmoothRep.universeLift.{uW} As
  let D' := SmoothRep.universeLift.{uV} Ds
  let eA := SmoothRep.universeLiftEquiv.{uW} As
  let eD := SmoothRep.universeLiftEquiv.{uV} Ds
  have hA'a : A'.IsAdmissible :=
    (SmoothRep.isAdmissible_universeLift_iff As).mpr hAa
  have hD'i : D'.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff Ds).mpr hDi
  have hD'c : IsLeviCuspidal B D'.representation :=
    (isLeviCuspidal_iff_of_equiv B eD).mp hDc
  have hD'A' : SmoothRep.IsSubquotient D' A' := by
    obtain ⟨S, q, hq⟩ := hDA
    let X := SmoothRep.subrepresentation As S
    let X' := SmoothRep.universeLift.{uW} X
    let eX := SmoothRep.universeLiftEquiv.{uW} X
    let i := eA.toIntertwiningMap.comp
      ((SmoothRep.hom (SmoothRep.subtype As S)).comp eX.symm.toIntertwiningMap)
    let q' := eD.toIntertwiningMap.comp (q.comp eX.symm.toIntertwiningMap)
    exact SmoothRep.isSubquotient_iff_exists.mpr
      ⟨X', SmoothRep.ofHom i, SmoothRep.ofHom q',
        eA.injective.comp ((SmoothRep.subtype_injective As S).comp eX.symm.injective),
        eD.surjective.comp (hq.comp eX.symm.surjective)⟩
  obtain ⟨⟨i, hi⟩, ⟨q, hq⟩⟩ :=
    leviCuspidalConstituentTheorem F T B A' D' hA'a hD'i hD'c hD'A'
  exact ⟨
    ⟨eA.symm.toIntertwiningMap.comp ((SmoothRep.hom i).comp eD.toIntertwiningMap),
      eA.symm.injective.comp (hi.comp eD.injective)⟩,
    ⟨eD.symm.toIntertwiningMap.comp ((SmoothRep.hom q).comp eA.toIntertwiningMap),
      eD.symm.surjective.comp (hq.comp eA.surjective)⟩⟩

/-- A chosen embedding and quotient, with their actual injectivity and
surjectivity certificates, for a cuspidal constituent in any carrier universe. -/
def leviCuspidalConstituentMaps :
    letI := T.topology
    ∀ (A : Rep.{uV} ℂ (B.Levi F.Carrier))
      (D : Rep.{uW} ℂ (B.Levi F.Carrier)),
      IsAdmissible A.ρ → Representation.IsIrreducible D.ρ →
      IsLeviCuspidal B D.ρ →
      (∃ S : Subrepresentation A.ρ,
        ∃ q : S.toRepresentation.IntertwiningMap D.ρ, Function.Surjective q) →
      {i : D.ρ.IntertwiningMap A.ρ // Function.Injective i} ×
        {q : A.ρ.IntertwiningMap D.ρ // Function.Surjective q} := by
  letI := T.topology
  intro A D hAa hDi hDc hDA
  let h := leviCuspidalConstituent_maps F T B A D hAa hDi hDc hDA
  exact ⟨⟨h.1.choose, h.1.choose_spec⟩, ⟨h.2.choose, h.2.choose_spec⟩⟩

end Langlands.CuspidalSupport
