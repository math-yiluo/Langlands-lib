import Langlands.Cohomology.AnalyticEtaleGaloisGermCover
import Langlands.Cohomology.AnalyticEtaleGaloisGermSections
import Langlands.Cohomology.FilteredGaloisAcyclicity
import Langlands.Geometry.Analytic.DistinguishedEtaleActionLift
import Langlands.Geometry.Analytic.EtalePointwiseLifting.Proof
import Langlands.Geometry.Analytic.QuasiEtaleActionLiftProof
import Langlands.Sheaf.Equivariant.TwistedFiniteRestrictionSections

/-! # Acyclicity on relative finite Galois germs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Set TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z a w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}

/-- The ordinary restriction of an étale G-sheaf, with its ordinary sheaf condition. -/
abbrev ordinaryEtaleRestriction {R : Type w} [CommRing R]
    (S : EtaleGSheaf ρ (ModuleCat.{w} R)) :
    Sheaf (etaleTopology X) (ModuleCat.{w} R) :=
  (TwistedOver.restriction ρ (etaleTopology X) _).obj
    (((distinguishedLiftSystem ρ).smoothSheafInclusion _ (twistedEtaleTopology ρ)).obj S)

/-- The intersection of the discrete sieves of a family of sections. -/
def sectionFamilyDiscreteSieve {R : Type w} [CommRing R]
    (S : EtaleGSheaf ρ (ModuleCat.{w} R)) {A : EtaleSite X} {D : Type a}
    (s : D → S.obj.obj.obj (op ((ι etale ρ).obj A))) : Sieve ((ι etale ρ).obj A) :=
  ⨅ d, (distinguishedLiftSystem ρ).discreteSieve S.obj.obj (s d)

private theorem sectionFamilyDiscreteSieve_covering {R : Type w} [CommRing R]
    (S : EtaleGSheaf ρ (ModuleCat.{w} R)) {A : EtaleSite X} {D : Type a} [Finite D]
    (s : D → S.obj.obj.obj (op ((ι etale ρ).obj A))) :
    sectionFamilyDiscreteSieve S s ∈ twistedEtaleTopology ρ ((ι etale ρ).obj A) := by
  classical
  let := Fintype.ofFinite D
  let J := twistedEtaleTopology ρ
  let L := distinguishedLiftSystem ρ
  change (⨅ d, L.discreteSieve S.obj.obj (s d)) ∈ J ((ι etale ρ).obj A)
  rw [← Finset.inf_univ_eq_iInf]
  have h (t : Finset D) : t.inf (fun d => L.discreteSieve S.obj.obj (s d)) ∈ J ((ι etale ρ).obj A) := by
    induction t using Finset.induction_on with
    | empty => exact J.top_mem _
    | insert d t hd ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (S.property _ _) ih
  exact h Finset.univ

omit [TopologicalSpace G] in
private theorem twistedCovering_pullback_singleton {A B W : EtaleSite X}
    (r : B ⟶ A) (f : W ⟶ A)
    (hrange : ∀ x : (EtaleSite.points X).obj B,
      (EtaleSite.points X).map r x ∈ range ((EtaleSite.points X).map f)) :
    (Sieve.ofArrows (fun _ : Fin 1 => (ι etale ρ).obj W) (fun _ => (ι etale ρ).map f)).pullback
      ((ι etale ρ).map r) ∈ twistedEtaleTopology ρ ((ι etale ρ).obj B) := by
  change Sieve.functorPullback (ι etale ρ) _ ∈ etaleTopology X B
  apply mem_etaleTopology_of_jointlySurjective
  intro x
  obtain ⟨y, hy⟩ := hrange x
  obtain ⟨Z, p, q, h, z, hz, _⟩ := etalePointwiseLifting X r f x y hy.symm
  refine ⟨Z, p, ?_, ⟨z, hz⟩⟩
  change Sieve.ofArrows (fun _ : Fin 1 => (ι etale ρ).obj W) (fun _ => (ι etale ρ).map f)
    ((ι etale ρ).map p ≫ (ι etale ρ).map r)
  exact ⟨(ι etale ρ).obj W, (ι etale ρ).map q, (ι etale ρ).map f, ⟨0⟩, by
    rw [← (ι etale ρ).map_comp, ← (ι etale ρ).map_comp, h]⟩

variable {y : localizedSpaceFunctor.obj X} {V : EtaleGermNeighborhood X y}

private def stageDeckAut (E : EtaleGermGaloisCover V)
    {U : Opens (localizedSpaceFunctor.obj X)} (hU : U ≤ E.baseOpen) :
    E.Γ →* Aut (((etaleOpenRestrictionFunctor X).obj U).obj E.source.obj).left := by
  let d := E.stageCover hU
  refine
    { toFun := fun γ =>
        { asIso.hom := (d.deck γ).left
          asIso.inv := (d.deck γ⁻¹).left
          asIso.hom_inv_id := congrArg (fun f => f.left) (show d.deck γ ≫ d.deck γ⁻¹ = 𝟙 _ by
            rw [← d.deck_mul, inv_mul_cancel, d.deck_one])
          asIso.inv_hom_id := congrArg (fun f => f.left) (show d.deck γ⁻¹ ≫ d.deck γ = 𝟙 _ by
            rw [← d.deck_mul, mul_inv_cancel, d.deck_one]) }
      map_one' := Aut.ext (Iso.ext (congrArg (fun f => f.left) d.deck_one))
      map_mul' := fun γ δ => Aut.ext (Iso.ext (congrArg (fun f => f.left) (d.deck_mul γ δ))) }

variable {L : Type uL} [NormedField L] [NormedAlgebra K L]
variable [IsTopologicalGroup G] [T2Space (localizedSpaceFunctor.obj X)]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable {R : Type (max u (v + 1) uL)} [CommRing R]
variable (S : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))

/-- Coinduction on fixed sections gives vanishing positive deck cohomology
on a supplied relative analytic Galois germ cover. -/
theorem isZero_groupCohomology_relativeGaloisGerm
    (hρ : IsContinuousAction ρ) (hS : HasCoinducedGaloisFixedSections L S)
    (E : EtaleGermGaloisCover V) (n : ℕ) :
    IsZero (groupCohomology
      ((EtaleGermGaloisCover.toGermCover.{u, v, uL, z} E R hρ).action.rep
        (ordinaryEtaleRestriction S)) (n + 1)) := by
  classical
  have := etale_hasSheafify.{u, v, uL} X R
  let := distinguishedNbhdIndex_isCofiltered.{u, v, uL} hρ E.mem_baseOpen
  let F := ordinaryEtaleRestriction S
  let D := EtaleGermGaloisCover.germDatum.{u, v, uL} E
  let A := EtaleGermGaloisCover.toGermCover.{u, v, uL, z} E R hρ
  refine IsZero.of_iso ?_
    ((groupCohomology.functor R A.Γ (n + 1)).mapIso (A.repIso F))
  change IsZero (groupCohomology ((D.action R).rep F) (n + 1))
  apply CoinducedFilteredAcyclic.isZero_groupCohomology_of_eventually_acyclic_subrepresentation
    (D.repCoconeIsColimit R F)
  intro i s
  let U := (nbhdOpen.{u, v, uL} X y).obj i.unop.obj
  let P := E.source.restrict U (mem_nbhdOpen X y i.unop.obj)
  let M := sectionFamilyDiscreteSieve S (A := P.obj) s
  have hM : Sieve.functorPullback (ι etale ρ) M ∈ etaleTopology X P.obj :=
    sectionFamilyDiscreteSieve_covering S (A := P.obj) s
  obtain ⟨W, f, hf, w, hw⟩ := jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting
    (etalePointwiseLifting (K := K)) _ hM P.point
  let B : Opens (localizedSpaceFunctor.obj P.obj.left) :=
    ⟨range (localizedSpaceFunctor.map f.left),
      (etaleOpenMap K f.left (EtaleSite.etale_left f)).isOpen_range⟩
  obtain ⟨O, hy, hO⟩ := P.shrink B ⟨w, hw⟩
  have hyOU : y ∈ (O ⊓ U : Opens _) := ⟨hy, mem_nbhdOpen X y i.unop.obj⟩
  obtain ⟨j, ⟨q⟩⟩ := exists_distinguishedNbhdIndex.{u, v, uL} hρ E.mem_baseOpen
    (nbhdIndex.mk (O ⊓ U) hyOU)
  have hj : (nbhdOpen.{u, v, uL} X y).obj j.obj ≤ O ⊓ U :=
    leOfHom ((nbhdOpen.{u, v, uL} X y).map q)
  let b : j ⟶ i.unop := ObjectProperty.homMk (nbhdIndex.homOfLE (hj.trans inf_le_right))
  let r := (EtaleGermGaloisCover.coverDiagram.{u, v, uL} E).map b
  have hcov := twistedCovering_pullback_singleton (ρ := ρ) r f (fun x => by
    let C := (EtaleGermGaloisCover.coverDiagram.{u, v, uL} E).obj j
    change localizedSpaceFunctor.obj C.left at x
    apply hO
    change localizedSpaceFunctor.map P.obj.hom (localizedSpaceFunctor.map r.left x) ∈ O
    have hx : localizedSpaceFunctor.map P.obj.hom (localizedSpaceFunctor.map r.left x) =
        localizedSpaceFunctor.map C.hom x :=
      (localizedSpaceFunctor.map_comp_apply r.left P.obj.hom x).symm.trans
        (congrArg (fun k : C.left ⟶ X => localizedSpaceFunctor.map k x)
          (MorphismProperty.Over.w r))
    have hx' : localizedSpaceFunctor.map C.hom x =
        localizedSpaceFunctor.map E.source.obj.hom x.val :=
      restrictEtale_hom_apply X ((nbhdOpen X y).obj j.obj) E.source.obj x
    exact (congrArg (fun t => t ∈ O) (hx.trans hx')).mpr ((hj.trans inf_le_left) x.property))
  have hdisc d : (distinguishedLiftSystem ρ).discreteSieve S.obj.obj (s d) ((ι etale ρ).map f) :=
    (iInf_le (fun d => (distinguishedLiftSystem ρ).discreteSieve S.obj.obj (s d)) d)
      ((ι etale ρ).map f) hf
  have hLift (U : LocalizedCategory.{u, v, v} (K := K)) (p : U ⟶ X)
      (h : quasiEtale p) (hc : IsCompactSpace U) : Nonempty (ActionLift ρ p) :=
    (quasiEtaleActionLift G X U ρ p inferInstance hρ h hc).1
  have hdU := E.distinguished_stage i.unop
  have hdT := E.distinguished_stage j
  obtain ⟨lU⟩ := nonempty_actionLift_of_isDistinguishedEtale hLift hdU
  obtain ⟨lT⟩ := nonempty_actionLift_of_isDistinguishedEtale hLift hdT
  let rt := (ι etale ρ).map r
  have ha : (distinguishedLiftSystem ρ).IsAdmissible ((ι etale ρ).obj P.obj)
      (liftOpenSubgroup lU) (liftAction lU) :=
    ⟨hdU, lU, le_rfl, MonoidHom.ext fun _ => rfl⟩
  have hb : (distinguishedLiftSystem ρ).IsAdmissible ((ι etale ρ).obj _) (liftOpenSubgroup lT)
      (liftAction lT) :=
    ⟨hdT, lT, le_rfl, MonoidHom.ext fun _ => rfl⟩
  let t := fun d => S.obj.obj.map rt.op (s d)
  have ht d : IsDiscreteSection S.obj.obj (liftAction lT) (t d) :=
    isDiscreteSection_restriction_of_finite_discreteSieve_cover
      (isLiftSystem_liftSystem (ρ := ρ) fun Y => IsDistinguishedEtale Y.hom)
      S.obj.property ha hb rt (s d)
      ⟨1, fun _ => (ι etale ρ).obj W, fun _ => (ι etale ρ).map f, fun _ => hdisc d, hcov⟩
  let deck := stageDeckAut E j.property.1
  have hdeck γ : (deck γ).asIso.hom ≫ ((EtaleGermGaloisCover.coverDiagram.{u, v, uL} E).obj j).hom =
      ((EtaleGermGaloisCover.coverDiagram.{u, v, uL} E).obj j).hom :=
    MorphismProperty.Over.w ((E.stageCover j.property.1).deck γ)
  have hfree (γ : E.Γ) (p : (localizedFieldPointFunctor L).obj
      ((EtaleGermGaloisCover.coverDiagram.{u, v, uL} E).obj j).left)
      (hp : (localizedFieldPointFunctor L).map (deck γ).asIso.hom p = p) : γ = 1 := by
    let Fp := localizedFieldPointFunctor (K := K) L
    let inc := restrictEtaleInclusion X ((nbhdOpen X y).obj j.obj) E.source.obj
    change Fp.map ((E.stageCover j.property.1).deck γ).left p = p at hp
    apply E.geometry.eq_one_of_fieldPoint_fixed (L := L) γ (Fp.map inc p)
    rw [← Fp.map_comp_apply, ← E.stageDeck_comp_inclusion j.property.1,
      Fp.map_comp_apply]
    exact congrArg (fun q => Fp.map inc q) hp
  let σ := (D.coveringAt j).representation F
  have hσ (γ : ULift.{max u (v + 1) uL} E.Γ) (x : (D.repDiagram R F).obj (op j)) :
      σ γ x = S.obj.obj.map
        (deckEndomorphism _ (deck γ.down⁻¹).asIso (hdeck γ.down⁻¹)).op x := rfl
  obtain ⟨N, a, hmono, hz, hmem⟩ :=
    exists_galoisFixedSubrepresentation_of_discreteSections hS hdT lT deck hdeck hfree σ hσ t ht n
  exact ⟨op j, b.op, N, a, hmono, hz, hmem⟩

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
