import Langlands.Representation.Filtration.QuotientFirstIso
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof

/-!
# The two-step Mackey sequence for the mirabolic restriction

A natural filtration of length two whose graded pieces are naturally isomorphic
to `A` and `B` gives natural maps `A ⟶ F ⟶ B` that are injective, exact in the
middle and surjective at every object. Applied to the published closed-subgroup
Mackey filtration of compact induction from the binary parabolic restricted to
the mirabolic subgroup, with the two-orbit ordering, this gives the sequence
`orbitPiece (open) → restricted compact induction → orbitPiece (closed)`.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV uR uG uC vC

namespace RepFunctorFiltration

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

/-- A two-step natural filtration with identified graded pieces gives a natural
short exact sequence. -/
theorem exists_exact_of_two (s : RepFunctorFiltration F 2) {A B : C ⥤ Rep.{uV} R G}
    (e₀ : s.graded 0 ≅ A) (e₁ : s.graded 1 ≅ B) :
    ∃ (i : A ⟶ F) (q : F ⟶ B), ∀ X,
      Function.Injective (i.app X).hom ∧
      LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
      Function.Surjective (q.app X).hom := by
  let S₀ := s.step (0 : Fin 2).castSucc
  let S₁ := s.step (0 : Fin 2).succ
  let S₂ := s.step (1 : Fin 2).succ
  let e₀' : S₀.quotientFunctor S₁ ≅ A := e₀
  let e₁' : S₁.quotientFunctor S₂ ≅ B := e₁
  have hzero : ∀ X, S₀.obj X = ⊥ := s.zero
  have htop : ∀ X, S₂.obj X = ⊤ := s.top
  have hker : ∀ (X : C) (v : S₁.representation X),
      v ∈ S₀.lowerInUpper S₁ X ↔
        ((𝟙 S₁.toFunctor : S₁.toFunctor ⟶ S₁.toFunctor).app X).hom v = 0 := by
    intro X v
    change v.val ∈ (S₀.obj X).toSubmodule ↔ v = 0
    rw [hzero X]
    change v.val ∈ (⊥ : Submodule R (F.obj X)) ↔ v = 0
    rw [Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let lift₀ : S₀.quotientFunctor S₁ ⟶ S₁.toFunctor :=
    S₀.quotientNatLift S₁ (𝟙 _) (fun X v => (hker X v).mp)
  have hlift : ∀ X, Function.Bijective (lift₀.app X).hom :=
    S₀.quotientNatLift_bijective S₁ (𝟙 _) hker (fun X => fun v => ⟨v, rfl⟩)
  have he₀ : ∀ X x, (e₀'.hom.app X).hom ((e₀'.inv.app X).hom x) = x :=
    fun X x => Rep.hom_inv_apply _ _ (e₀'.app X) x
  have he₀' : ∀ X x, (e₀'.inv.app X).hom ((e₀'.hom.app X).hom x) = x :=
    fun X x => Rep.inv_hom_apply _ _ (e₀'.app X) x
  have he₁ : ∀ X x, (e₁'.hom.app X).hom ((e₁'.inv.app X).hom x) = x :=
    fun X x => Rep.hom_inv_apply _ _ (e₁'.app X) x
  have he₁' : ∀ X x, (e₁'.inv.app X).hom ((e₁'.hom.app X).hom x) = x :=
    fun X x => Rep.inv_hom_apply _ _ (e₁'.app X) x
  let toTop : F ⟶ S₂.toFunctor :=
    { app := fun X => Rep.ofHom
        { toLinearMap :=
            { toFun := fun v => ⟨v, by
                change v ∈ (S₂.obj X).toSubmodule
                rw [htop X]
                exact Submodule.mem_top⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          isIntertwining' := fun _ => rfl }
      naturality := fun _ _ _ => rfl }
  refine ⟨e₀'.inv ≫ lift₀ ≫ S₁.inclusion,
    toTop ≫ S₁.quotientNatProjection S₂ ≫ e₁'.hom, fun X => ⟨?_, ?_, ?_⟩⟩
  · intro x y hxy
    have h1 : (lift₀.app X).hom ((e₀'.inv.app X).hom x) =
        (lift₀.app X).hom ((e₀'.inv.app X).hom y) := S₁.inclusion_injective X hxy
    have h2 := congrArg (e₀'.hom.app X).hom ((hlift X).1 h1)
    rwa [he₀, he₀] at h2
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      change (e₁'.hom.app X).hom ((S₁.quotientProjection S₂ X).hom ((toTop.app X).hom
        ((lift₀.app X).hom ((e₀'.inv.app X).hom z)).val)) = 0
      have hm : (toTop.app X).hom ((lift₀.app X).hom ((e₀'.inv.app X).hom z)).val ∈
          (S₁.lowerInUpper S₂ X).toSubmodule :=
        ((lift₀.app X).hom ((e₀'.inv.app X).hom z)).property
      have h0 : (S₁.quotientProjection S₂ X).hom ((toTop.app X).hom
          ((lift₀.app X).hom ((e₀'.inv.app X).hom z)).val) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hm
      rw [h0]
      exact map_zero _
    · intro hx
      change (e₁'.hom.app X).hom ((S₁.quotientProjection S₂ X).hom ((toTop.app X).hom x)) = 0
        at hx
      have hx' : (S₁.quotientProjection S₂ X).hom ((toTop.app X).hom x) = 0 := by
        have h := congrArg (e₁'.inv.app X).hom hx
        exact ((he₁' X _).symm.trans h).trans (map_zero _)
      have hmem' : (toTop.app X).hom x ∈ (S₁.lowerInUpper S₂ X).toSubmodule :=
        (Submodule.Quotient.mk_eq_zero _).mp hx'
      have hmem : x ∈ (S₁.obj X).toSubmodule := hmem'
      refine ⟨(e₀'.hom.app X).hom ((S₀.quotientProjection S₁ X).hom ⟨x, hmem⟩), ?_⟩
      change ((lift₀.app X).hom ((e₀'.inv.app X).hom ((e₀'.hom.app X).hom
        ((S₀.quotientProjection S₁ X).hom ⟨x, hmem⟩)))).val = x
      exact (congrArg (fun z => ((lift₀.app X).hom z).val)
        (he₀' X ((S₀.quotientProjection S₁ X).hom ⟨x, hmem⟩))).trans rfl
  · intro y
    obtain ⟨w, hw⟩ := S₁.quotientProjection_surjective S₂ X ((e₁'.inv.app X).hom y)
    refine ⟨w.val, ?_⟩
    change (e₁'.hom.app X).hom ((S₁.quotientProjection S₂ X).hom ((toTop.app X).hom w.val)) = y
    have hw' : (toTop.app X).hom w.val = w := rfl
    rw [hw', hw, he₁]

end RepFunctorFiltration

namespace Derivative.MirabolicProductRestriction

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The Mackey sequence for compact induction from the binary parabolic restricted
to the mirabolic subgroup: the open-orbit piece, the whole restriction, and the
closed-orbit piece. -/
theorem exists_exact_restrictedCompactInduction (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n) (openRep F.Carrier m n) ⟶
        Geometric.restrictedCompactInduction (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n))
      (q : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n) ⟶
        Geometric.orbitPiece (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean ((m + 1) + (n + 1))
  let := T.generalLinearLocallyCompactSpace ((m + 1) + (n + 1))
  let := T.generalLinearT2Space ((m + 1) + (n + 1))
  let := T.generalLinearSigmaCompactSpace ((m + 1) + (n + 1))
  have hP : IsClosed (parabolicP F.Carrier m n : Set (GeneralLinear ((m + 1) + (n + 1)) F.Carrier)) :=
    (shape m n).isClosed_parabolic F.Carrier
  have hQ : IsClosed (mirabolicQ F.Carrier m n : Set (GeneralLinear ((m + 1) + (n + 1)) F.Carrier)) :=
    Mirabolic.isClosed
  have hM := Geometric.closedSubgroupMackeyFiltration.{uF, uV}
    (GeneralLinear ((m + 1) + (n + 1)) F.Carrier) (parabolicP F.Carrier m n)
    (mirabolicQ F.Carrier m n) hP hQ 2 (orbitOrdering m n)
  obtain ⟨e₀⟩ := hM 0
  obtain ⟨e₁⟩ := hM 1
  exact RepFunctorFiltration.exists_exact_of_two _ e₀ e₁

end Derivative.MirabolicProductRestriction

end Langlands
