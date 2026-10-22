import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Quasicuspidality is preserved by actual smooth Levi subquotients. -/

namespace Langlands.CuspidalSupport

open GeneralLinear CategoryTheory

universe uF uV uW

variable {F : Type uF} [Field F] {n : ℕ} (B : BlockShape n)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A surjective intertwiner induces a surjection on every actual subgroup
coinvariant quotient. This step uses no smoothness. -/
theorem coinvariants_map_surjective
    {ρ : Representation ℂ (B.Levi F) V}
    {σ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (N : Subgroup (B.Levi F)) :
    Function.Surjective (Representation.Coinvariants.map _ _ (Jacquet.restrictMap f N)) := by
  intro w
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective σ N w
  obtain ⟨u, rfl⟩ := hf v
  exact ⟨Jacquet.mk ρ N u, rfl⟩

section Smooth

variable [TopologicalSpace F]

/-- The actual quotient of a quasicuspidal smooth representation is
quasicuspidal. -/
theorem isLeviQuasicuspidal_quotient
    {A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)}
    (S : Subrepresentation A.representation)
    (hA : IsLeviQuasicuspidal B A.representation) :
    IsLeviQuasicuspidal B (SmoothRep.quotient A S).representation :=
  isLeviQuasicuspidal_of_surjective B (SmoothRep.hom (SmoothRep.mkQ A S))
    (SmoothRep.mkQ_surjective A S) hA

/-- Transfer along the actual categorical isomorphism retained in a smooth
subquotient witness. -/
theorem isLeviQuasicuspidal_iff_of_iso
    {A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F)} (e : D ≅ A) :
    IsLeviQuasicuspidal B D.representation ↔
      IsLeviQuasicuspidal B A.representation :=
  isLeviQuasicuspidal_iff_of_equiv B (SmoothRep.equivOfIso e)

end Smooth

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Quasicuspidality passes to an actual smooth invariant submodule, by
injectivity of every refined unipotent coinvariant map. -/
theorem isLeviQuasicuspidal_subrepresentation :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (S : Subrepresentation A.representation),
      IsLeviQuasicuspidal B A.representation →
        IsLeviQuasicuspidal B (SmoothRep.subrepresentation A S).representation := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro A S hA R hR
  let N := Geometric.refinedUnipotent F.Carrier B R
  let i := Jacquet.restrictMap (SmoothRep.hom (SmoothRep.subtype A S)) N
  have hi : Function.Injective i := SmoothRep.subtype_injective A S
  have hsm : IsSmooth (A.representation.comp N.subtype) :=
    isSmooth_comp N.subtype continuous_subtype_val A.isSmooth
  have hinj := coinvariants_map_injective_of_smooth
    (T.refinedUnipotent_finite_containment B R) i hi hsm
  let := hA R hR
  exact Function.Injective.subsingleton hinj

end Padic

/-- The exact published subquotient-closure proposition, with no additional
representation hypotheses and with rank zero included. -/
theorem leviQuasicuspidalSubquotient {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviQuasicuspidalSubquotientTheorem.{uF, uV} F T B := by
  let := T.topology
  intro A D hA hD
  obtain ⟨S, Q, ⟨e⟩⟩ := hD
  apply (isLeviQuasicuspidal_iff_of_iso B e).mpr
  exact isLeviQuasicuspidal_quotient B Q
    (isLeviQuasicuspidal_subrepresentation B F T A S hA)

end Langlands.CuspidalSupport
