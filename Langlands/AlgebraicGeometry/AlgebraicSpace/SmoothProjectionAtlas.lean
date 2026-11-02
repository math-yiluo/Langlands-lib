import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement

/-! # Smooth endpoint atlases obtained from a smooth scheme cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

variable {S : Scheme.{u}} {U : Over S}

/-- An actual etale atlas on which both relation projections are smooth. -/
structure SmoothProjectionAtlas (R : AlgebraicSpace S)
    (s t : R.presheaf ⟶ (schemeYoneda S).obj U) where
  source : Over S
  atlas : (schemeYoneda S).obj source ⟶ R.presheaf
  fst : source ⟶ U
  snd : source ⟶ U
  etale : IsEtale atlas
  surjective : IsSurjective atlas
  fst_fac : atlas ≫ s = (schemeYoneda S).map fst
  snd_fac : atlas ≫ t = (schemeYoneda S).map snd
  fst_smooth : Smooth fst.left
  snd_smooth : Smooth snd.left

/-- The actual atlas data supplies the generic quotient hypothesis. -/
lemma SmoothProjectionAtlas.hasSmoothProjections {R : AlgebraicSpace S}
    {s t : R.presheaf ⟶ (schemeYoneda S).obj U} (a : SmoothProjectionAtlas R s t) :
    HasSmoothProjections R s t :=
  ⟨a.source, a.atlas, a.fst, a.snd, a.etale, a.surjective,
    a.fst_fac, a.snd_fac, a.fst_smooth, a.snd_smooth⟩

variable
  (hDescent : ∀ (P W V : Scheme.{u}) (p : P ⟶ W) (g : W ⟶ V),
    Smooth p → Surjective p → Smooth (p ≫ g) → Smooth g)
  (R : AlgebraicSpace S) (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
  {A : Over S} (q : (schemeYoneda S).obj A ⟶ R.presheaf)
  (hq : IsSmooth q) (hqSurj : IsSurjective q)
  (sA tA : A ⟶ U)
  (hsA : q ≫ s = (schemeYoneda S).map sA)
  (htA : q ≫ t = (schemeYoneda S).map tA)
  (hsmooth : Smooth sA.left) (htsmooth : Smooth tA.left)

/-- A smooth surjective scheme cover with smooth composite endpoints supplies
an actual etale smooth-projection atlas, assuming smooth-source descent. -/
def smoothProjectionAtlasOfSmoothCover : SmoothProjectionAtlas R s t := by
  apply Classical.choice
  obtain ⟨W, b, hb, hbSurj⟩ := R.property.2
  let P := hq.representable.pullback b
  let p : P ⟶ W := hq.representable.snd b
  obtain ⟨a, ha⟩ := (schemeYoneda S).map_surjective (hq.representable.fst b)
  have hPB : IsPullback ((schemeYoneda S).map a) ((schemeYoneda S).map p) q b := by
    rw [ha]
    exact hq.representable.isPullback b
  let : Smooth p.left := hq.projection b ((schemeYoneda S).map a) p hPB
  let : Surjective p.left := hqSurj.projection b ((schemeYoneda S).map a) p hPB
  let : Etale a.left := hb.projection q ((schemeYoneda S).map p) a hPB.flip
  obtain ⟨sW, hsW⟩ := (schemeYoneda S).map_surjective (b ≫ s)
  obtain ⟨tW, htW⟩ := (schemeYoneda S).map_surjective (b ≫ t)
  have hps : p ≫ sW = a ≫ sA := by
    apply (schemeYoneda S).map_injective
    simp only [Functor.map_comp]
    rw [hsW, ← Category.assoc, ← hPB.w, Category.assoc, hsA]
  have hpt : p ≫ tW = a ≫ tA := by
    apply (schemeYoneda S).map_injective
    simp only [Functor.map_comp]
    rw [htW, ← Category.assoc, ← hPB.w, Category.assoc, htA]
  let : Smooth sA.left := hsmooth
  let : Smooth tA.left := htsmooth
  have hpsmooth : Smooth (p.left ≫ sW.left) := by
    change Smooth (p ≫ sW).left
    rw [hps]
    change Smooth (a.left ≫ sA.left)
    infer_instance
  have hptsmooth : Smooth (p.left ≫ tW.left) := by
    change Smooth (p ≫ tW).left
    rw [hpt]
    change Smooth (a.left ≫ tA.left)
    infer_instance
  exact ⟨
    { source := W
      atlas := b
      fst := sW
      snd := tW
      etale := hb
      surjective := hbSurj
      fst_fac := hsW.symm
      snd_fac := htW.symm
      fst_smooth := hDescent P.left W.left U.left p.left sW.left
        inferInstance inferInstance hpsmooth
      snd_smooth := hDescent P.left W.left U.left p.left tW.left
        inferInstance inferInstance hptsmooth }⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
