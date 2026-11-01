import Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionStatement
import Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement
import Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The global closed-immersion criterion from the local one

The local criterion `ProperRationalImmersionLocalClosedImmersionStatement` gives, for each
rational point `x` of `X`, an open neighbourhood `V_x` of `f x` in `Y` over which `f` is a
closed immersion. Together with the open complement of the closed image of `f`, these opens
cover every closed point of the Jacobson space `Y`, hence cover `Y`, and being a closed
immersion is local on the target. Applying this to the published proof
`properRationalImmersion_localClosedImmersion` of the local criterion gives the target
`properRationalImmersion_isClosedImmersion`.
-/

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry

/-- The global closed-immersion criterion follows from the local criterion at rational
points. -/
theorem properRationalImmersion_isClosedImmersion_of
    (hLoc : ProperRationalImmersionLocalClosedImmersionStatement.{u}) :
    ProperRationalImmersionClosedImmersionStatement.{u} := by
  intro K _ _ X Y p q _ _ f _ hfq hpt htan
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  let ι := {x : Spec (CommRingCat.of K) ⟶ X // Picard.IsRationalPoint p x}
  have hV : ∀ x : ι, ∃ V : Y.Opens,
      f.base (x.1.base (IsLocalRing.closedPoint K)) ∈ V ∧ IsClosedImmersion (f ∣_ V) :=
    fun x => hLoc K X Y p q f hfq x.1 x.2 (fun y hy hyx => hpt y x.1 hy x.2 hyx)
      (fun t ht htf => htan x.1 x.2 t ht htf)
  choose V hxV hVci using hV
  -- The complement of the (closed) image of `f`.
  let V₀ : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  let W : Option ι → Y.Opens := fun o => o.elim V₀ V
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W ?_ ?_
  · rw [eq_top_iff]
    by_contra hne
    have hS : ((⨆ o, W o : Y.Opens) : Set Y)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      apply hne
      intro y _
      rw [← SetLike.mem_coe, h]
      trivial
    obtain ⟨y, hyS, hy⟩ :=
      nonempty_inter_closedPoints hS (⨆ o, W o).isOpen.isClosed_compl.isLocallyClosed
    apply hyS
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    by_cases hyf : y ∈ Set.range f
    · obtain ⟨x₀, rfl⟩ := hyf
      have hF : (f ⁻¹' {f x₀}).Nonempty := ⟨x₀, rfl⟩
      obtain ⟨x₁, hx₁f, hx₁⟩ :=
        nonempty_inter_closedPoints hF (hy.preimage f.continuous).isLocallyClosed
      let r : ι := ⟨pointOfClosedPoint p x₁ hx₁, pointOfClosedPoint_comp p x₁ hx₁⟩
      have hr : f.base (r.1.base (IsLocalRing.closedPoint K)) = f x₀ := by
        have h₁ : r.1.base (IsLocalRing.closedPoint K) = x₁ :=
          pointOfClosedPoint_apply p x₁ hx₁ _
        rw [h₁]
        exact hx₁f
      refine ⟨some r, ?_⟩
      have hmem := hxV r
      rw [hr] at hmem
      exact hmem
    · exact ⟨none, hyf⟩
  · rintro (_ | x)
    · have : IsEmpty (f ⁻¹ᵁ W none) := ⟨fun z => z.2 ⟨z.1, rfl⟩⟩
      infer_instance
    · exact hVci x

/-- A proper morphism of schemes locally of finite type over an algebraically closed field
that is injective on rational points and on rational tangent vectors is a closed immersion. -/
theorem properRationalImmersion_isClosedImmersion :
    ProperRationalImmersionClosedImmersionStatement.{u} :=
  properRationalImmersion_isClosedImmersion_of properRationalImmersion_localClosedImmersion.{u}

end Langlands.AlgebraicGeometry
