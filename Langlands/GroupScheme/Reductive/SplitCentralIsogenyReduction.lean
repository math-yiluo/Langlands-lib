import Langlands.GroupScheme.Reductive.SplitClassificationStatement
import Langlands.GroupScheme.Reductive.SplitIsomorphismStatement
import Langlands.GroupScheme.Reductive.CentralTorusQuotientStatement
import Langlands.GroupScheme.Reductive.RootDatumHomLattices
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumStatement
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Torus.CharacterMapHom

/-! # Reduction of the central Isogeny Theorem to the Isomorphism Theorem -/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- **Central Isogeny Theorem from the Isomorphism Theorem.** The split central Isogeny Theorem
follows from four statements: existence of root data, the root-datum morphism of a central
isogeny, the central quotient by the kernel of a torus isogeny, and the Isomorphism Theorem for
two groups sharing a split maximal torus. -/
def splitCentralIsogenyExistence_of_commonTorusIsomorphism
    (hRD : RootDatumExistenceStatement.{u}) (hHom : CentralIsogenyRootDatumHomStatement.{u})
    (hQuot : SplitCentralTorusQuotientStatement.{u})
    (hIso : SplitCommonTorusIsomorphismStatement.{u}) :
    SplitCentralIsogenyExistenceStatement.{u} := by
  intro k _ G G' hG hG' T T' hT hT' i i' hi hi' J J' P P' hP hP' f hfw hfc
  -- The torus map `t : T ⟶ T'` whose character pullback is the weight map of `f`.
  obtain ⟨t, ht⟩ := hT'.exists_hom_of_characterMap f.weightMap.toAddMonoidHom
  have hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ := fun χ => (ht χ).symm
  have hcw : ∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t :=
    RootDatumHom.coweightMap_apply_of_weightMap hP'.1 hP.1 f t hw
  -- The central quotient `q : G ⟶ Q` with maximal torus `i'' : T' ⟶ Q`.
  have hinjX : Function.Injective (fun χ : characterLattice T' => t ≫ χ) := by
    intro χ ψ h
    apply hfw
    simpa only [hw] using h
  have hinjY : Function.Injective (fun ν : cocharacterLattice T => ν ≫ t) := by
    intro ν μ h
    apply hfc
    simpa only [hcw] using h
  have hroots : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∃ α' : characterLattice T', α = t ≫ α' := by
    intro α hα
    rw [← hP.2.1] at hα
    obtain ⟨j, rfl⟩ := hα
    refine ⟨P'.root (f.indexEquiv.symm j), ?_⟩
    rw [← hw, RootPairing.Hom.root_weightMap_apply, Equiv.apply_symm_apply]
  obtain ⟨Q, hQ, q, i'', hi'', hq, hqt⟩ := hQuot k G hG T T' hT hT' i hi t hinjX hinjY hroots
  -- A root datum `P''` of `i''`, and the morphism of root data `P'' ⟶ P` defined by `q`.
  obtain ⟨J'', _, P'', hP'', -⟩ := hRD k Q hQ T' hT' i'' hi''
  obtain ⟨f'', hw'', hcw'', -, -, -⟩ :=
    hHom k G Q hG hQ T T' hT hT' i i'' hi hi'' q t hq hqt J J'' P P'' hP hP''
  -- `P''` and `P'` are root data on `T'` matching under `J'' ≃ J ≃ J'`.
  let e : J'' ≃ J' := f''.indexEquiv.trans f.indexEquiv.symm
  have he_root : ⇑P'.root ∘ ⇑e = ⇑P''.root := by
    funext j
    apply hfw
    simp only [Function.comp_apply, e, Equiv.trans_apply]
    rw [RootPairing.Hom.root_weightMap_apply, Equiv.apply_symm_apply, hw, ← hw'',
      RootPairing.Hom.root_weightMap_apply]
  have he_coroot : ⇑P'.coroot ∘ ⇑e = ⇑P''.coroot := by
    funext j
    simp only [Function.comp_apply, e, Equiv.trans_apply]
    rw [← RootPairing.Hom.coroot_coweightMap_apply, hcw, ← hcw'',
      RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
  -- The Isomorphism Theorem identifies `Q` with `G'` over `T'`.
  obtain ⟨ψ, hψ⟩ := hIso k Q G' hQ hG' T' hT' i'' i' hi'' hi' J'' J' P'' P' hP'' hP' e
    he_root he_coroot
  refine ⟨q ≫ ψ.hom, t, ?_, hw, hq.comp_iso ψ⟩
  rw [← Category.assoc, hqt, Category.assoc, hψ]

end Langlands.GroupScheme
