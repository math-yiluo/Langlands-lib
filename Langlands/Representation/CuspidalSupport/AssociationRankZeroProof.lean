import Langlands.Representation.CuspidalSupport.AssociationRankZeroStatement

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear CategoryTheory

universe uF uV uW uR uG

private theorem rankZero_empty (B : BlockShape 0) : IsEmpty (Fin B.length) :=
  ⟨fun i => Fin.elim0 (B.index i ⟨0, B.positive i⟩)⟩

private theorem rankZero_levi_subsingleton (F : Type uF) [Field F]
    (B : BlockShape 0) : Subsingleton (B.Levi F) := by
  let := rankZero_empty B
  infer_instance

private def subsingletonInducedEquiv
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Subsingleton G]
    (P : Subgroup G) {V : Type uV} [AddCommGroup V] [Module R V]
    (σ : Representation R P V) : Induction.SmoothFunctions P σ ≃ₗ[R] V where
  toFun f := Induction.eval P σ f 1
  invFun v := Induction.smoothFunctionOf P σ (fun _ => v)
    (by intro p x; have hp : p = 1 := Subsingleton.elim _ _; simp [hp])
    ⊤ (by intros; rfl)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrArg (Induction.eval P σ f) (Subsingleton.elim _ _)
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def oneStepFiltration {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    (A : Rep.{uV} R G) : ObjectRepFiltration A 1 :=
  ObjectRepFiltration.ofSubrepresentations
    (fun i => if i = 0 then ⊥ else ⊤)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by simp) (by simp)

private def oneStepGradedEquiv {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    (A : Rep.{uV} R G) (i : Fin 1) :
    ((oneStepFiltration A).gradedRepresentation i).ρ.Equiv A.ρ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let q : Submodule R (⊤ : Submodule R A) :=
    (⊥ : Submodule R A).comap (⊤ : Subrepresentation A.ρ).toSubmodule.subtype
  have hq : q = ⊥ := by
    ext v
    change (v.val = 0) ↔ v = 0
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine Representation.Equiv.mk
    ((q.quotEquivOfEqBot hq).trans Submodule.topEquiv) ?_
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := (oneStepFiltration A).gradedProjection_surjective 0 v
  rfl

private def trivialSubrepresentationOrderIso
    {G : Type uG} [Monoid G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Subrepresentation ρ ≃o Submodule ℂ V where
  toFun := Subrepresentation.toSubmodule
  invFun S := ⟨S, by
    intro g v hv
    have hg : g = 1 := Subsingleton.elim _ _
    simpa [hg] using hv⟩
  left_inv S := by cases S; rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

private theorem trivialIrreducible_iff
    {G : Type uG} [Monoid G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    Representation.IsIrreducible ρ ↔ IsSimpleModule ℂ V := by
  rw [isSimpleModule_iff]
  exact (trivialSubrepresentationOrderIso ρ).isSimpleOrder_iff

private theorem simpleScalarEquiv (V : Type uV) [AddCommGroup V] [Module ℂ V]
    [IsSimpleModule ℂ V] : Nonempty (ℂ ≃ₗ[ℂ] V) := by
  let := IsSimpleModule.nontrivial ℂ V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v)
    ⟨smul_left_injective ℂ hv, IsSimpleModule.toSpanSingleton_surjective ℂ hv⟩⟩

private def trivialRepresentationEquiv
    {G : Type uG} [Monoid G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (e : V ≃ₗ[ℂ] W) : ρ.Equiv τ := by
  refine Representation.Equiv.mk e ?_
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  ext v
  simp [hg]

/-- The exact association equivalences at rank zero. -/
theorem cuspidalInductionAssociationRankZero :
    CuspidalInductionAssociationRankZeroStatement.{uF, uV, uW} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup 0
  intro B C σ τ hσ _ hτ _
  let := rankZero_levi_subsingleton F.Carrier B
  let := rankZero_levi_subsingleton F.Carrier C
  let hσs : IsSimpleModule ℂ σ := (trivialIrreducible_iff σ.representation).mp hσ
  let hτs : IsSimpleModule ℂ τ := (trivialIrreducible_iff τ.representation).mp hτ
  obtain ⟨eσ⟩ := simpleScalarEquiv σ
  obtain ⟨eτ⟩ := simpleScalarEquiv τ
  have hassoc : RepresentationsAssociated B C σ.representation τ.representation := by
    have hw : ConjugatesLevi (F := F.Carrier) B C 1 := Subsingleton.elim _ _
    exact ⟨1, hw, ⟨trivialRepresentationEquiv _ _ (eσ.symm.trans eτ)⟩⟩
  let σP := twist (T.parabolicHalfModulus B)
    (σ.representation.comp (B.leviProjection F.Carrier))
  let τP := twist (T.parabolicHalfModulus C)
    (τ.representation.comp (C.leviProjection F.Carrier))
  let π := Induction.smoothInduced (B.parabolic F.Carrier) σP
  let π' := Induction.smoothInduced (C.parabolic F.Carrier) τP
  let A := SmoothRep.of π (Induction.smoothInduced_smooth _ σP)
  let A' := SmoothRep.of π' (Induction.smoothInduced_smooth _ τP)
  let Eσ := subsingletonInducedEquiv (B.parabolic F.Carrier) σP
  let Eτ := subsingletonInducedEquiv (C.parabolic F.Carrier) τP
  let hπs : IsSimpleModule ℂ A := Eσ.isSimpleModule_iff.mpr hσs
  let hπ's : IsSimpleModule ℂ A' := Eτ.isSimpleModule_iff.mpr hτs
  let e : π.Equiv π' :=
    trivialRepresentationEquiv π π' (Eσ.trans ((eσ.symm.trans eτ).trans Eτ.symm))
  have hhom : ∃ f : π.IntertwiningMap π', f ≠ 0 := by
    refine ⟨e.toIntertwiningMap, ?_⟩
    intro he
    let := IsSimpleModule.nontrivial ℂ A
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply e.injective
    have hev := congrArg (fun f : π.IntertwiningMap π' => f v) he
    simpa using hev
  let s := oneStepFiltration (Rep.of π)
  let t := oneStepFiltration (Rep.of π')
  have hs : s.HasSimpleFactors := by
    intro i
    exact (trivialIrreducible_iff _).mpr
      ((oneStepGradedEquiv (Rep.of π) i).toLinearEquiv.isSimpleModule_iff.mpr hπs)
  have ht : t.HasSimpleFactors := by
    intro i
    exact (trivialIrreducible_iff _).mpr
      ((oneStepGradedEquiv (Rep.of π') i).toLinearEquiv.isSimpleModule_iff.mpr hπ's)
  have he (i : Fin 1) :
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (t.gradedRepresentation i).ρ) :=
    ⟨(oneStepGradedEquiv (Rep.of π) i).trans
      (e.trans (oneStepGradedEquiv (Rep.of π') i).symm)⟩
  have hjh : HaveSameJordanHolderFactors (Rep.of π) (Rep.of π') :=
    ⟨1, s, t, hs, ht, 1, he⟩
  have hcommon :
      ∃ (S : Subrepresentation A.representation)
        (Q : Subrepresentation (SmoothRep.subrepresentation A S).representation)
        (S' : Subrepresentation A'.representation)
        (Q' : Subrepresentation (SmoothRep.subrepresentation A' S').representation),
        (SmoothRep.subquotient A S Q).IsIrreducible ∧
        Nonempty ((SmoothRep.subquotient A S Q).representation.Equiv
          (SmoothRep.subquotient A' S' Q').representation) := by
    let i : Fin 1 := 0
    exact ⟨s.subrepresentation i.succ,
      (s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit),
      t.subrepresentation i.succ,
      (t.step i.castSucc).lowerInUpper (t.step i.succ) (Discrete.mk PUnit.unit),
      hs i, he i⟩
  exact ⟨⟨fun _ => hhom, fun _ => hassoc⟩,
    ⟨fun _ => hjh, fun _ => hassoc⟩, ⟨fun _ => hcommon, fun _ => hassoc⟩⟩

end Langlands.CuspidalSupport
