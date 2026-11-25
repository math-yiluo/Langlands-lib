import Langlands.Cohomology.AnalyticEtaleGaloisFixedSections
import Langlands.Geometry.Analytic.EtaleCoveringPoints.Statement
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Sheaf.Equivariant.AnalyticEtaleOpenRestriction
import Langlands.Sheaf.Equivariant.TwistedFiniteRestrictionSections

/-! # Finite families of discrete restrictions after shrinking the base -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z w a

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {R : Type w} [CommRing R] (S : EtaleGSheaf ρ (ModuleCat.{w} R))

private abbrev plainDeck {V : EtaleSite X} (e : Aut V.left) (he : e.asIso.hom ≫ V.hom = V.hom) :
    V ⟶ V := MorphismProperty.Over.homMk e.asIso.hom he

omit [TopologicalSpace G] in
private theorem deckEndomorphism_eq_map {V : EtaleSite X} (e : Aut V.left)
    (he : e.asIso.hom ≫ V.hom = V.hom) :
    deckEndomorphism ((ι etale ρ).obj V) e.asIso he = (ι etale ρ).map (plainDeck e he) :=
  hom_ext rfl rfl

private theorem restrict_point_inj (T : Opens (localizedSpaceFunctor.obj X)) (V : EtaleSite X) :
    Function.Injective ((EtaleSite.points X).map ((etaleOpenRestrictionInclusion X T).app V)) := by
  intro p q hpq
  exact Subtype.ext hpq

/-- The common discrete sieve for the deck translates of the sections in a family. -/
def deckTranslateDiscreteSieve {V : EtaleSite X} {Γ D : Type a}
    (deck : Γ → Aut V.left) (hdeck : ∀ γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
    (s : D → S.obj.obj.obj (op ((ι etale ρ).obj V))) :
    Sieve ((ι etale ρ).obj V) :=
  ⨅ i : D × Γ, (distinguishedLiftSystem ρ).discreteSieve S.obj.obj
    (S.obj.obj.map (deckEndomorphism ((ι etale ρ).obj V) (deck i.2).asIso (hdeck i.2)).op (s i.1))

/-- If covering sieves lift ordinary points and the deck family is
transitive on each fibre, a finite family of sections has a common finite
family of discrete restrictions that covers after shrinking the base. -/
theorem exists_open_finite_discreteSieve_family
    (hpoints : EtaleCoveringPointsStatement.{u, v} K)
    {V : EtaleSite X} {Γ : Type a} [Finite Γ]
    (deck : Γ → Aut V.left) (hdeck : ∀ γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
    (htrans : ∀ x y : localizedSpaceFunctor.obj V.left,
      localizedSpaceFunctor.map V.hom x = localizedSpaceFunctor.map V.hom y →
        ∃ γ, localizedSpaceFunctor.map (deck γ).asIso.hom x = y)
    {D : Type a} [Finite D] (s : D → S.obj.obj.obj (op ((ι etale ρ).obj V)))
    (x : localizedSpaceFunctor.obj V.left) :
    ∃ O : Opens (localizedSpaceFunctor.obj X), localizedSpaceFunctor.map V.hom x ∈ O ∧
      ∃ (n : ℕ) (W : Fin n → TwistedOver etale ρ) (f : ∀ j, W j ⟶ (ι etale ρ).obj V),
        (∀ i j, (distinguishedLiftSystem ρ).discreteSieve S.obj.obj (s i) (f j)) ∧
        ∀ T : Opens (localizedSpaceFunctor.obj X), T ≤ O →
          (Sieve.ofArrows W f).pullback ((ι etale ρ).map ((etaleOpenRestrictionInclusion X T).app V))
            ∈ twistedEtaleTopology ρ ((ι etale ρ).obj (((etaleOpenRestrictionFunctor X).obj T).obj V)) := by
  classical
  let := Fintype.ofFinite Γ
  let := Fintype.ofFinite D
  let J := twistedEtaleTopology ρ
  let dS (i : D × Γ) := (distinguishedLiftSystem ρ).discreteSieve S.obj.obj
    (S.obj.obj.map (deckEndomorphism ((ι etale ρ).obj V) (deck i.2).asIso (hdeck i.2)).op (s i.1))
  have hdS (t : Finset (D × Γ)) : t.inf dS ∈ J ((ι etale ρ).obj V) := by
    induction t using Finset.induction_on with
    | empty => exact J.top_mem _
    | insert i t hi ht =>
        rw [Finset.inf_insert]
        exact J.intersection_covering (S.property _ _) ht
  let E := deckTranslateDiscreteSieve S deck hdeck s
  have hE : Sieve.functorPullback (ι etale ρ) E ∈ etaleTopology X V := by
    change E ∈ J ((ι etale ρ).obj V)
    change (⨅ i, dS i) ∈ J ((ι etale ρ).obj V)
    rw [← Finset.inf_univ_eq_iInf]
    exact hdS Finset.univ
  obtain ⟨W, f, hf, w, hw⟩ := hpoints X _ hE x
  let O : Opens (localizedSpaceFunctor.obj X) :=
    ⟨Set.range (localizedSpaceFunctor.map W.hom), (etaleOpenMap K W.hom W.prop).isOpen_range⟩
  have hw' : localizedSpaceFunctor.map f.left w = x := hw
  have hW (z : localizedSpaceFunctor.obj W.left) :
      localizedSpaceFunctor.map W.hom z =
        localizedSpaceFunctor.map V.hom (localizedSpaceFunctor.map f.left z) := by
    rw [← localizedSpaceFunctor.map_comp_apply, MorphismProperty.Over.w f]
  let e := Fintype.equivFin Γ
  let p (j : Fin (Fintype.card Γ)) := f ≫ plainDeck (deck (e.symm j)) (hdeck (e.symm j))
  refine ⟨O, ⟨w, (hW w).trans (congrArg (localizedSpaceFunctor.map V.hom) hw')⟩,
    Fintype.card Γ, fun _ => (ι etale ρ).obj W, fun j => (ι etale ρ).map (p j), ?_, ?_⟩
  · intro i j
    have hs : dS (i, e.symm j) ((ι etale ρ).map f) :=
      (iInf_le dS (i, e.symm j)) ((ι etale ρ).map f) hf
    have hres := (distinguishedLiftSystem ρ).discreteSieve_le_pullback S.obj.obj
      (deckEndomorphism ((ι etale ρ).obj V) (deck (e.symm j)).asIso (hdeck (e.symm j))) (s i)
      ((ι etale ρ).map f) hs
    change (distinguishedLiftSystem ρ).discreteSieve S.obj.obj (s i)
      ((ι etale ρ).map f ≫ deckEndomorphism ((ι etale ρ).obj V) (deck (e.symm j)).asIso _) at hres
    rw [deckEndomorphism_eq_map, ← (ι etale ρ).map_comp] at hres
    exact hres
  · intro T hTO
    let Q := (etaleOpenRestrictionFunctor X).obj T
    let r := etaleOpenRestrictionInclusion X T
    change Sieve.functorPullback (ι etale ρ)
      ((Sieve.ofArrows (fun _ => (ι etale ρ).obj W) (fun j => (ι etale ρ).map (p j))).pullback
        ((ι etale ρ).map (r.app V))) ∈ etaleTopology X (Q.obj V)
    apply mem_etaleTopology_of_jointlySurjective
    intro z
    let y : (EtaleSite.points X).obj V := (EtaleSite.points X).map (r.app V) z
    have hy : localizedSpaceFunctor.map V.hom y ∈ T := z.property
    obtain ⟨b, hb⟩ := hTO hy
    have hbT : localizedSpaceFunctor.map W.hom b ∈ T := hb ▸ hy
    obtain ⟨γ, hγ⟩ := htrans (localizedSpaceFunctor.map f.left b) y ((hW b).symm.trans hb)
    let j := e γ
    let b' : (EtaleSite.points X).obj (Q.obj W) := ⟨b, hbT⟩
    refine ⟨Q.obj W, Q.map (p j), ?_, ⟨b', ?_⟩⟩
    · change Sieve.ofArrows (fun _ => (ι etale ρ).obj W) (fun i => (ι etale ρ).map (p i))
        ((ι etale ρ).map (Q.map (p j)) ≫ (ι etale ρ).map (r.app V))
      refine ⟨(ι etale ρ).obj W, (ι etale ρ).map (r.app W), (ι etale ρ).map (p j), ⟨j⟩, ?_⟩
      rw [← (ι etale ρ).map_comp, ← (ι etale ρ).map_comp, r.naturality]
      rfl
    · apply restrict_point_inj T V
      change (EtaleSite.points X).map (r.app V) ((EtaleSite.points X).map (Q.map (p j)) b') = y
      have hbase : (EtaleSite.points X).map (p j) ((EtaleSite.points X).map (r.app W) b') = y := by
        change localizedSpaceFunctor.map (f.left ≫ (deck (e.symm j)).asIso.hom) b = y
        rw [localizedSpaceFunctor.map_comp_apply, show e.symm j = γ from e.symm_apply_apply γ]
        exact hγ
      calc
        _ = (EtaleSite.points X).map (Q.map (p j) ≫ r.app V) b' :=
          ((EtaleSite.points X).map_comp_apply (Q.map (p j)) (r.app V) b').symm
        _ = (EtaleSite.points X).map (r.app W ≫ p j) b' :=
          congrArg (fun g => (EtaleSite.points X).map g b') (r.naturality (p j))
        _ = (EtaleSite.points X).map (p j) ((EtaleSite.points X).map (r.app W) b') :=
          (EtaleSite.points X).map_comp_apply (r.app W) (p j) b'
        _ = y := hbase

variable [IsTopologicalGroup G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- A finite family of sections becomes discrete after shrinking to a smaller
distinguished stage with a supplied action lift. -/
theorem exists_open_discrete_on_restriction
    (hpoints : EtaleCoveringPointsStatement.{u, v} K)
    {V : EtaleSite X} (hV : IsDistinguishedEtale V.hom) (l : ActionLift ρ V.hom)
    {Γ : Type a} [Finite Γ] (deck : Γ → Aut V.left) (hdeck : ∀ γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
    (htrans : ∀ x y : localizedSpaceFunctor.obj V.left,
      localizedSpaceFunctor.map V.hom x = localizedSpaceFunctor.map V.hom y →
        ∃ γ, localizedSpaceFunctor.map (deck γ).asIso.hom x = y)
    {D : Type a} [Finite D] (s : D → S.obj.obj.obj (op ((ι etale ρ).obj V)))
    (x : localizedSpaceFunctor.obj V.left) :
    ∃ O : Opens (localizedSpaceFunctor.obj X), localizedSpaceFunctor.map V.hom x ∈ O ∧
      ∀ T : Opens (localizedSpaceFunctor.obj X), T ≤ O →
        let V' := (((etaleOpenRestrictionFunctor X).obj T).obj V)
        IsDistinguishedEtale V'.hom → ∀ l' : ActionLift ρ V'.hom, ∀ i,
          IsDiscreteSection S.obj.obj (liftAction (U := (ι etale ρ).obj V') l')
            (S.obj.obj.map ((ι etale ρ).map ((etaleOpenRestrictionInclusion X T).app V)).op (s i)) := by
  obtain ⟨O, hx, n, W, f, hf, hcov⟩ :=
    exists_open_finite_discreteSieve_family S hpoints deck hdeck htrans s x
  refine ⟨O, hx, fun T hTO hV' l' i => ?_⟩
  let V' := (((etaleOpenRestrictionFunctor X).obj T).obj V)
  have ha : (distinguishedLiftSystem ρ).IsAdmissible ((ι etale ρ).obj V)
      (liftOpenSubgroup l) (liftAction l) :=
    ⟨hV, l, le_rfl, MonoidHom.ext fun _ => rfl⟩
  have ha' : (distinguishedLiftSystem ρ).IsAdmissible ((ι etale ρ).obj V')
      (liftOpenSubgroup l') (liftAction l') :=
    ⟨hV', l', le_rfl, MonoidHom.ext fun _ => rfl⟩
  exact isDiscreteSection_restriction_of_finite_discreteSieve_cover
    (isLiftSystem_liftSystem (ρ := ρ) fun Z => IsDistinguishedEtale Z.hom)
    S.obj.property ha ha' _ (s i) ⟨n, W, f, hf i, hcov T hTO⟩

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
