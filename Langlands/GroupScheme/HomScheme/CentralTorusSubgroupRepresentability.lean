import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleCriterion
import Langlands.GroupScheme.HomScheme.CentralAdmissibleAdicLimits
import Langlands.GroupScheme.HomScheme.CentralAdmissibleFilteredColimits

/-! # Separated étale representability of central closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}

/-- A central family is universal if every actual central closed torus subgroup
functor on every test has a unique parameter with the same all-test subgroup. -/
def IsCentralUniversal {H : GroupScheme M.left}
    (j : H ⟶ (baseChange M.hom).obj G) : Prop :=
  ∀ (T : Over S) (F : SubgroupFunctor ((baseChange T.hom).obj G)),
    IsAdmissible F → F ≤ center ((baseChange T.hom).obj G) →
      ∃! a : T ⟶ M, evaluate j a = F

private def centralAdmissibleEquiv (G : GroupScheme S) (T : Over S) :
    (smallCentralAdmissiblePresheaf G).obj (op T) ≃
      {F : AdmissibleSubgroup ((baseChange T.hom).obj G) // F.val ≤ center _} where
  toFun x := ⟨smallAdmissibleEquiv G T x.val, x.property⟩
  invFun F := ⟨(smallAdmissibleEquiv G T).symm F.val, by
    change (smallAdmissibleEquiv G T ((smallAdmissibleEquiv G T).symm F.val)).val ≤ center _
    rw [Equiv.apply_symm_apply]
    exact F.property⟩
  left_inv x := Subtype.ext ((smallAdmissibleEquiv G T).symm_apply_apply x.val)
  right_inv F := Subtype.ext ((smallAdmissibleEquiv G T).apply_symm_apply F.val)

/-- Decode a representative of the central presheaf into an actual universal
closed central torus inclusion. -/
theorem exists_centralUniversal_of_representableBy
    (e : (smallCentralAdmissiblePresheaf G).RepresentableBy M) :
    ∃ (H : GroupScheme M.left) (j : H ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus H ∧ IsCentral j ∧ IsCentralUniversal j := by
  let x := e.homEquiv (𝟙 M)
  let r := admissibleRepresentative (smallAdmissibleEquiv G M x.val)
  refine ⟨r.group, r.hom, r.closed, r.torus, (mem_centralAdmissible_iff x.val).mp x.property, ?_⟩
  intro T F hF hc
  let E := e.homEquiv.trans (centralAdmissibleEquiv G T)
  let y : {F : AdmissibleSubgroup ((baseChange T.hom).obj G) // F.val ≤ center _} := ⟨⟨F, hF⟩, hc⟩
  have hEval (a : T ⟶ M) : (E a).val.val = evaluate r.hom a := by
    have ha : e.homEquiv a = (smallCentralAdmissiblePresheaf G).map a.op x := by
      simpa only [Category.comp_id] using e.homEquiv_comp a (𝟙 M)
    change (smallAdmissibleEquiv G T (e.homEquiv a).val).val = evaluate r.hom a
    rw [ha]
    change (smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op x.val)).val =
      evaluate r.hom a
    rw [smallAdmissibleEquiv_map]
    exact restrict_eq_evaluate _ r.hom r.represents.2 a
  refine ⟨E.symm y, ?_, fun a ha => ?_⟩
  · change evaluate r.hom (E.symm y) = F
    rw [← hEval, Equiv.apply_symm_apply]
  · apply E.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (Subtype.ext ((hEval a).trans ha))

/-- Over a locally noetherian base, adic limits for all torus subgroups and
infinitesimal bijectivity for central ones suffice for a separated étale
parameter scheme with an actual universal central closed torus. -/
def EtaleCentralTorusSubgroupRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom],
    AdicLimits (smallAdmissiblePresheaf G) → ArtinianNilpotentBijective (smallCentralAdmissiblePresheaf G) →
    ∃ (Y : Scheme.{u}) (q : Y ⟶ S) (H : GroupScheme Y) (j : H ⟶ (baseChange q).obj G),
      IsSeparated q ∧ Etale q ∧ IsClosedSubgroup j ∧ RelativeTorus.IsTorus H ∧
        IsCentral j ∧ IsCentralUniversal (M := Over.mk q) j

/-- Apply Murre's separated étale criterion to the actual central subpresheaf
and evaluate the corresponding universal section. -/
theorem etaleCentralTorusSubgroupRepresentability :
    EtaleCentralTorusSubgroupRepresentabilityStatement.{u} := by
  intro S _ G _ _ _ _ hadic hArtinian
  obtain ⟨Y, q, ⟨e⟩, hsep, hetale⟩ := murreEtaleCriterion S (smallCentralAdmissiblePresheaf G)
    (fun _ => inferInstance) (smallCentralAdmissiblePresheaf_zariskiSheaf G)
    (smallCentralAdmissiblePresheaf_faithfullyFlatSheaf G)
    (smallCentralAdmissiblePresheaf_filteredColimits S G)
    (centralAdmissible_adicLimits_of_admissible G hadic)
    (smallCentralAdmissiblePresheaf_valuativeSeparation G) hArtinian
  obtain ⟨H, j, hj, hH, hc, hu⟩ := exists_centralUniversal_of_representableBy e
  exact ⟨Y, q, H, j, hsep, hetale, hj, hH, hc, hu⟩

end Langlands.GroupScheme.TorusSubgroupModuli
