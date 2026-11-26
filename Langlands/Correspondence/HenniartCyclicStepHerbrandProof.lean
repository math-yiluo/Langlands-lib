import Langlands.Correspondence.HenniartCyclicStepHerbrandStatement

/-!
# The relative Herbrand function of a cyclic prime-degree step

The normal closure of the intermediate field is the field itself. The relative
function therefore reduces to the inverse Herbrand function over the base, which
is invariant under the given algebra equivalence.
-/

namespace Langlands.Henniart

open LocalClassField Ramification.HerbrandBridge Ramification.Padic

universe u v

private theorem herbrandPhi_eq_self_of_surjective {p : ℕ} [Fact p.Prime]
    {L : PadicField.{u} p} (T : L.TopologicalData) (K : Type v)
    [Field K] [Algebra (Padic p) K] [Algebra K L.Carrier]
    [IsScalarTower (Padic p) K L.Carrier]
    (h : Function.Surjective (algebraMap K L.Carrier)) (x : ℝ) : herbrandPhi T K x = x := by
  let : Subsingleton (L.Carrier ≃ₐ[K] L.Carrier) := ⟨fun σ τ => AlgEquiv.ext fun y => by
    obtain ⟨z, rfl⟩ := h y
    rw [σ.commutes, τ.commutes]⟩
  have horder (i : ℕ) : lowerGroupOrder T K i = 1 := Nat.card_unique
  rcases le_total x 0 with hx | hx
  · exact herbrandPhi_of_nonpos T K hx
  · rw [herbrandPhi_floor T K hx]
    simp only [horder, Nat.cast_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, div_one]
    ring

attribute [local instance] asPadicField_isScalarTower

/-- The inverse Herbrand function of the step agrees with the relative function
of the isomorphic intermediate field. -/
theorem cyclicPrimeStepHerbrandPsi : CyclicPrimeStepHerbrandPsiStatement.{u} := by
  intro p hp S E h
  let := S.algebra
  let := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  let := S.isGalois
  obtain ⟨f⟩ := h
  let : Normal S.base.Carrier E.field := Normal.of_algEquiv f
  have hclosure : (galoisClosure E).toIntermediateField = E.field :=
    IntermediateField.normalClosure_of_normal E.field
  let K := E.asPadicField (p := p)
  let : Algebra (Padic p) K.Carrier := K.algebra
  let N := extendFiniteGalois (algebraMap_mem_galoisClosure E)
  let T := (finiteGaloisPadicField K N).canonicalTopologicalData
  let : Algebra (Padic p) N := (finiteGaloisPadicField K N).algebra
  let : IsScalarTower (Padic p) K.Carrier N := N.toIntermediateField.isScalarTower
  let : IsScalarTower (Padic p) S.base.Carrier N :=
    extension_padicScalarTower S.base K N
  have hsurj : Function.Surjective (algebraMap K.Carrier N) := by
    intro x
    have hx : (x : AlgebraicClosure S.base.Carrier) ∈ (galoisClosure E).toIntermediateField :=
      x.property
    rw [hclosure] at hx
    exact ⟨⟨(x : AlgebraicClosure S.base.Carrier), hx⟩, Subtype.ext rfl⟩
  let e : S.top.Carrier ≃ₐ[S.base.Carrier] N :=
    (f.trans (IntermediateField.equivOfEq hclosure.symm)).trans
      (extendFiniteGaloisEquiv (algebraMap_mem_galoisClosure E))
  funext x
  change herbrandPsi S.top.canonicalTopologicalData S.base.Carrier x =
    herbrandPhi T K.Carrier (herbrandPsi T S.base.Carrier x)
  rw [herbrandPhi_eq_self_of_surjective T K.Carrier hsurj]
  exact (herbrandPsi_eq_of_algEquiv S.top.canonicalTopologicalData T S.base.Carrier e x).symm

end Langlands.Henniart
