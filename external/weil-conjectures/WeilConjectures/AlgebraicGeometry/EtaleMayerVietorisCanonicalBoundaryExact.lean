/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisCanonicalBoundary
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalRestriction
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Exactness of the boundary of a fixed normalized resolution

Source: Stacks Project, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem exact_transport
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (ea : A ≃+ A') (eb : B ≃+ B') (ec : C ≃+ C')
    {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}
    (hf : ∀ x, eb (f x) = f' (ea x)) (hg : ∀ x, ec (g x) = g' (eb x))
    (hex : Function.Exact f g) : Function.Exact f' g' := by
  intro b
  constructor
  · intro hb
    have hz : g (eb.symm b) = 0 := by
      apply ec.injective
      simpa only [map_zero, hg, eb.apply_symm_apply] using hb
    obtain ⟨a, ha⟩ := (hex (eb.symm b)).mp hz
    refine ⟨ea a, ?_⟩
    rw [← hf, ha, eb.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := ea.surjective a
    rw [← hf, ← hg, (hex (f x)).mpr ⟨x, rfl⟩, map_zero]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- The constructed boundary is exact on both sides for the actual restrictions.
Source: Stacks Project, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-exact)

Proof: The fixed resolution gives a short exact sequence of section complexes.
Homology preserves their biproduct, identifying the middle homology with the
product of the two open homologies. Canonical comparison restriction identities
identify the two horizontal maps with the restriction pair and difference.
Transport homology exactness at the intersection and at the successor whole
term along these additive equivalences. The transported connecting map is
precisely the constructed boundary. This applies to empty and coincident opens. -/
private theorem etaleMayerVietorisCanonicalBoundary_exact {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (c : ResolutionSectionCanonicalComparison F I) (q : ℕ) :
    Function.Exact (fun (x :
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj F) q) ↦
      openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) F q x.1 -
      openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) F q x.2)
      (etaleMayerVietorisCanonicalBoundary U V hcover F I c q) ∧
    Function.Exact (etaleMayerVietorisCanonicalBoundary U V hcover F I c q)
      (fun x ↦ (cohomologyMap U.ι F (q + 1) x, cohomologyMap V.ι F (q + 1) x)) := by
  let S := etaleSectionShortComplex U V I.cocomplex
  let hS := etaleSectionShortComplex_resolution_shortExact U V hcover F I
  let K := ((etaleSectionFunctor (Scheme.Etale.mk U.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let L := ((etaleSectionFunctor (Scheme.Etale.mk V.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let eHom (n : ℕ) : (K ⊞ L).homology n ≃+ (K.homology n × L.homology n) :=
    (((HomologicalComplex.homologyFunctor _ _ n).mapBiprod K L) ≪≫
      AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv
  let eB (n : ℕ) := (eHom n).trans
    ((c.openEquiv U n).prodCongr (c.openEquiv V n))
  obtain ⟨hr, hd⟩ := resolutionSection_canonical_restriction F I c
  have hcoords (q : ℕ) (x : (K ⊞ L).homology q) :
      eHom q x =
        (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) q x,
         HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) q x) := by
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℕ) q
    have hf : (AddCommGrpCat.biprodIsoProd (K.homology q) (L.homology q)).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) = biprod.fst := by
      rw [← cancel_epi (AddCommGrpCat.biprodIsoProd _ _).inv]
      simp
    have hs : (AddCommGrpCat.biprodIsoProd (K.homology q) (L.homology q)).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) = biprod.snd := by
      rw [← cancel_epi (AddCommGrpCat.biprodIsoProd _ _).inv]
      simp
    apply Prod.ext
    · change (((H.mapBiprod K L).hom ≫ (AddCommGrpCat.biprodIsoProd _ _).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x) = (H.map biprod.fst) x
      erw [hf]
      exact congrArg (fun f ↦ f x) (Functor.biprodComparison_fst H K L)
    · change (((H.mapBiprod K L).hom ≫ (AddCommGrpCat.biprodIsoProd _ _).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x) = (H.map biprod.snd) x
      erw [hs]
      exact congrArg (fun f ↦ f x) (Functor.biprodComparison_snd H K L)
  have hpair (n : ℕ) (x : S.X₁.homology n) :
      eB n (HomologicalComplex.homologyMap S.f n x) =
        (cohomologyMap U.ι F n (c.globalEquiv n x),
          cohomologyMap V.ι F n (c.globalEquiv n x)) := by
    dsimp only [S, etaleSectionShortComplex, eB, AddEquiv.trans_apply,
      AddEquiv.prodCongr]
    rw [hcoords]
    change (c.openEquiv U n _, c.openEquiv V n _) = _
    apply Prod.ext
    all_goals dsimp only [Prod.fst, Prod.snd]
    · rw [← AddCommGrpCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        biprod.lift_fst]
      exact hr U n x
    · rw [← AddCommGrpCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        biprod.lift_snd]
      exact hr V n x
  have hdiff (n : ℕ) (x : S.X₂.homology n) :
      c.openEquiv (U ⊓ V) n (HomologicalComplex.homologyMap S.g n x) =
        openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) F n (eB n x).1 -
          openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) F n (eB n x).2 := by
    dsimp only [S, etaleSectionShortComplex]
    dsimp only [eB, AddEquiv.trans_apply, AddEquiv.prodCongr]
    rw [hcoords]
    have neg_eval {A B : AddCommGrpCat.{u + 1}} (f : A ⟶ B) (y : A) :
        (-f) y = -f y := rfl
    simp only [biprod.desc_eq, HomologicalComplex.homologyMap_add,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg,
      AddCommGrpCat.hom_add_apply, AddCommGrpCat.comp_apply,
      neg_eval, ← sub_eq_add_neg]
    change c.openEquiv (U ⊓ V) n (_ - _) = _
    rw [map_sub, hd, hd]
    rfl
  have hboundary (n : ℕ) (x : S.X₃.homology n) :
      c.globalEquiv (n + 1) (hS.δ n (n + 1) rfl x) =
        etaleMayerVietorisCanonicalBoundary U V hcover F I c n
          (c.openEquiv (U ⊓ V) n x) := by
    change c.globalEquiv (n + 1) _ = c.globalEquiv (n + 1)
      ((hS.δ n (n + 1) rfl).hom
        ((c.openEquiv (U ⊓ V) n).symm (c.openEquiv (U ⊓ V) n x)))
    rw [AddEquiv.symm_apply_apply]
  constructor
  · exact exact_transport (eB q) (c.openEquiv (U ⊓ V) q) (c.globalEquiv (q + 1))
      (hdiff q) (hboundary q)
      ((ShortComplex.ab_exact_iff_function_exact _).mp (hS.homology_exact₃ q (q + 1) rfl))
  · exact exact_transport (c.openEquiv (U ⊓ V) q) (c.globalEquiv (q + 1)) (eB (q + 1))
      (hboundary q) (hpair (q + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).mp (hS.homology_exact₁ q (q + 1) rfl))

/-- Exactness with the intersection supplied by an equality.
Source: Stacks Project, Tag 0A50, the preceding exactness and intersection identification.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-exact)

Proof: Substitute the intersection equality and apply canonical boundary exactness.
The two inclusion proofs agree by proof irrelevance. -/
private theorem etaleMayerVietorisBoundaryOn_exact {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (c : ResolutionSectionCanonicalComparison F I) (q : ℕ) (hU : W ≤ U) (hV : W ≤ V)
    (d : (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj F) q) →
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q)
    (hd : ∀ x, d x = openCohomologyRestriction hU F q x.1 -
      openCohomologyRestriction hV F q x.2) :
    Function.Exact d (etaleMayerVietorisBoundaryOn U V W hW hcover F I c q) ∧
    Function.Exact (etaleMayerVietorisBoundaryOn U V W hW hcover F I c q)
      (fun x ↦ (cohomologyMap U.ι F (q + 1) x, cohomologyMap V.ι F (q + 1) x)) := by
  subst W
  have he : d = (fun x ↦ openCohomologyRestriction hU F q x.1 -
      openCohomologyRestriction hV F q x.2) := funext hd
  rw [he]
  exact etaleMayerVietorisCanonicalBoundary_exact U V hcover F I c q

/-- Exactness of the fixed boundary interface.
Source: Stacks Project, Tag 0A50, long exact cohomology sequence.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-exact)

Proof: Unfold only the fixed resolution choices and apply named-intersection exactness. -/
theorem etaleMayerVietorisFixedBoundary_exact {X : Scheme.{u}}
    (U V W : X.Opens) (hW : W = U ⊓ V) (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (hU : W ≤ U) (hV : W ≤ V)
    (d : (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj F) q) →
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q)
    (hd : ∀ x, d x = openCohomologyRestriction hU F q x.1 -
      openCohomologyRestriction hV F q x.2) :
    Function.Exact d (etaleMayerVietorisFixedBoundary U V W hW hcover F q) ∧
    Function.Exact (etaleMayerVietorisFixedBoundary U V W hW hcover F q)
      (fun x ↦ (cohomologyMap U.ι F (q + 1) x, cohomologyMap V.ι F (q + 1) x)) := by
  unfold etaleMayerVietorisFixedBoundary
  exact etaleMayerVietorisBoundaryOn_exact U V W hW hcover F _ _ q hU hV d hd

end AlgebraicGeometry.Etale
