import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonStatement
import Langlands.GroupScheme.Descent.Data

/-! # Actual transitions between affine pinned charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (q : U ⟶ T)
    {G H : GroupScheme T} (a : G ⟶ H) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst H.X.hom q =
      pullback.fst G.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Two ways of removing successive pullbacks have the same actual projections. -/
theorem pullbackComparison_comp {S T U V : Scheme.{u}}
    (a : T ⟶ S) (b : U ⟶ T) (d : U ⟶ S) (hd : b ≫ a = d)
    (q : V ⟶ U) (e : V ⟶ S) (he : q ≫ d = e) (G : GroupScheme S) :
    (baseChange q).mapIso (pullbackComparison a b d hd G) ≪≫
        pullbackComparison d q e he G =
      pullbackComparison b q (q ≫ b) rfl ((baseChange a).obj G) ≪≫
        pullbackComparison a (q ≫ b) e
          ((Category.assoc _ _ _).trans ((congrArg (fun k => q ≫ k) hd).trans he)) G := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
      Over.comp_left, Category.assoc, pullbackComparison_hom_fst,
      map_fst_assoc, pullbackComparison_hom_fst_assoc]
  · exact (Over.w
      (((baseChange q).mapIso (pullbackComparison a b d hd G) ≪≫
        pullbackComparison d q e he G).hom.hom.hom)).trans
      (Over.w
      ((pullbackComparison b q (q ≫ b) rfl ((baseChange a).obj G) ≪≫
        pullbackComparison a (q ≫ b) e
          ((Category.assoc _ _ _).trans ((congrArg (fun k => q ≫ k) hd).trans he)) G
        ).hom.hom.hom)).symm

end Descent

namespace AffinePinnedChart

open Descent AffinePinnedModel

variable {S T W : Scheme.{u}} {G : GroupScheme S}

/-- Identify the actual pullback of the original group with the pinned model
along any map to a chart over the base. -/
def identify (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) :
    (baseChange k).obj G ≅ C.model.groupOver f :=
  (pullbackComparison C.map f k hf G).symm ≪≫ (baseChange f).mapIso C.iso

/-- Further pullback of a chart identification agrees with direct identification. -/
theorem identify_pull (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) (q : W ⟶ T)
    (l : W ⟶ S) (hl : q ≫ k = l) :
    (pullbackComparison k q l hl G).symm ≪≫
        (baseChange q).mapIso (C.identify f k hf) ≪≫
        (baseChangeCompIso f q C.model.group).symm =
      C.identify (q ≫ f) l
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hf).trans hl)) := by
  have hc := pullbackComparison_comp C.map f k hf q l hl G
  have hn := pullbackComparison_naturality f q (q ≫ f) rfl C.iso.hom
  apply Iso.ext
  dsimp only [identify, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Functor.map_comp]
  change (pullbackComparison k q l hl G).inv ≫
      ((baseChange q).map (pullbackComparison C.map f k hf G).inv ≫
        (baseChange q).map ((baseChange f).map C.iso.hom)) ≫
      (pullbackComparison f q (q ≫ f) rfl C.model.group).hom = _
  have hi := congrArg Iso.inv hc
  dsimp only [Iso.trans_inv, Functor.mapIso_inv] at hi
  have hi' := congrArg
    (fun a => a ≫ (pullbackComparison f q (q ≫ f) rfl
      ((baseChange C.map).obj G)).hom) hi
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hi'
  calc
    _ = ((pullbackComparison k q l hl G).inv ≫
        (baseChange q).map (pullbackComparison C.map f k hf G).inv ≫
        (pullbackComparison f q (q ≫ f) rfl ((baseChange C.map).obj G)).hom) ≫
        (baseChange (q ≫ f)).map C.iso.hom := by
      simp only [Category.assoc, hn]
    _ = _ := congrArg (fun a => a ≫ (baseChange (q ≫ f)).map C.iso.hom) hi'

/-- The original comparison between two pinned charts on a common test scheme. -/
def comparison (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k) : Comparison f g :=
  (C.identify f k hf).symm ≪≫ D.identify g k hg

@[simp] theorem comparison_self (C : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (k : T ⟶ S) (hf : f ≫ C.map = k) :
    C.comparison C f f k hf hf = Iso.refl _ := by
  apply Iso.ext
  simp [comparison]

/-- The original chart comparisons compose on every common test scheme. -/
theorem comparison_trans (C D E : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (h : T ⟶ E.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (hh : h ≫ E.map = k) :
    C.comparison E f h k hf hh =
      C.comparison D f g k hf hg ≪≫ D.comparison E g h k hg hh := by
  apply Iso.ext
  simp [comparison]

/-- Original chart comparisons commute with arbitrary further pullback. -/
theorem comparison_pull (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullComparison (C.comparison D f g k hf hg) q =
      C.comparison D (q ≫ f) (q ≫ g) l
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hf).trans hl))
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hg).trans hl)) := by
  dsimp only [comparison]
  rw [← C.identify_pull f k hf q l hl, ← D.identify_pull g k hg q l hl]
  apply Iso.ext
  simp [pullComparison]

/-- Apply a supplied natural pinning correction to the actual chart comparison. -/
def correctedComparison (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k) : Comparison f g :=
  P.compare C.model D.model f g (C.comparison D f g k hf hg)

@[simp] theorem correctedComparison_self (P : RelativePinnedComparison.{u})
    (C : AffinePinnedChart G) (f : T ⟶ C.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) :
    correctedComparison P C C f f k hf hf = Iso.refl _ := by
  simp only [correctedComparison, comparison_self, P.compare_refl]

/-- Corrected comparisons compose on every common test scheme. -/
theorem correctedComparison_trans (P : RelativePinnedComparison.{u})
    (C D E : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (h : T ⟶ E.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (hh : h ≫ E.map = k) :
    correctedComparison P C E f h k hf hh =
      correctedComparison P C D f g k hf hg ≪≫
        correctedComparison P D E g h k hg hh := by
  simp only [correctedComparison, comparison_trans C D E f g h k hf hg hh,
    P.compare_trans]

/-- Corrected comparisons commute with arbitrary further pullback. -/
theorem correctedComparison_pull (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullComparison (correctedComparison P C D f g k hf hg) q =
      correctedComparison P C D (q ≫ f) (q ≫ g) l
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hf).trans hl))
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hg).trans hl)) := by
  simp only [correctedComparison, ← comparison_pull C D f g k hf hg q l hl,
    P.compare_pull]

/-- Express a corrected chart comparison as an actual automorphism of the
original group pulled back to the common test scheme. -/
def transition (P : RelativePinnedComparison.{u}) (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k) :
    (baseChange k).obj G ≅ (baseChange k).obj G :=
  C.identify f k hf ≪≫ correctedComparison P C D f g k hf hg ≪≫
    (D.identify g k hg).symm

@[simp] theorem transition_self (P : RelativePinnedComparison.{u})
    (C : AffinePinnedChart G) (f : T ⟶ C.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) :
    transition P C C f f k hf hf = Iso.refl _ := by
  apply Iso.ext
  simp [transition]

/-- The actual corrected chart transitions satisfy the cocycle identity. -/
theorem transition_trans (P : RelativePinnedComparison.{u})
    (C D E : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (h : T ⟶ E.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (hh : h ≫ E.map = k) :
    transition P C E f h k hf hh =
      transition P C D f g k hf hg ≪≫ transition P D E g h k hg hh := by
  apply Iso.ext
  simp [transition, correctedComparison_trans P C D E f g h k hf hg hh]

/-- The actual corrected transitions commute with further pullback. -/
theorem transition_pull (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hl hl (transition P C D f g k hf hg) =
      transition P C D (q ≫ f) (q ≫ g) l
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hf).trans hl))
        ((Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) hg).trans hl)) := by
  dsimp only [transition]
  rw [← C.identify_pull f k hf q l hl, ← D.identify_pull g k hg q l hl,
    ← correctedComparison_pull P C D f g k hf hg q l hl]
  apply Iso.ext
  simp [pullIso, pullComparison]

/-- The coordinate torus inclusion expressed in the original pulled-back group. -/
def torusInOriginal (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) :
    splitTorus T C.model.coordinates ⟶ (baseChange k).obj G :=
  C.model.inclusionOver f ≫ (C.identify f k hf).inv

/-- The positive-coroot cocharacter expressed in the original pulled-back group. -/
def cocharacterInOriginal (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) :
    (Gm T).toGrp ⟶ (baseChange k).obj G :=
  C.model.cocharacterOver f ≫ (C.identify f k hf).inv

/-- Corrected transitions carry the actual coordinate torus inclusions to each other. -/
theorem transition_torus (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k) :
    ∃ τ : splitTorus T C.model.coordinates ≅ splitTorus T D.model.coordinates,
      C.torusInOriginal f k hf ≫ (transition P C D f g k hf hg).hom =
        τ.hom ≫ D.torusInOriginal g k hg := by
  obtain ⟨τ, hτ⟩ := P.torus C.model D.model T f g (C.comparison D f g k hf hg)
  refine ⟨τ, ?_⟩
  simpa only [torusInOriginal, transition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, correctedComparison] using
    congrArg (fun a => a ≫ (D.identify g k hg).inv) hτ

/-- Corrected transitions carry the actual positive-coroot cocharacters to each other. -/
theorem transition_cocharacter (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k) :
    C.cocharacterInOriginal f k hf ≫ (transition P C D f g k hf hg).hom =
      D.cocharacterInOriginal g k hg := by
  simpa only [cocharacterInOriginal, transition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, correctedComparison] using
    congrArg (fun a => a ≫ (D.identify g k hg).inv)
      (P.cocharacter C.model D.model T f g (C.comparison D f g k hf hg))

end AffinePinnedChart

end Langlands.GroupScheme
