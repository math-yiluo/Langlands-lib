import Langlands.Geometry.FormalGroup.DeligneLatticeCoherence
import Langlands.Geometry.FormalGroup.DeligneStructuralCoherence
import Langlands.Geometry.FormalGroup.DeligneComparisonCoherence

/-! # Coherent pullback of Deligne's four preliminary sheaf data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' S'' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- Assemble actual framed-lattice and graded-tangent isomorphisms with their
forward total-u square. The inverse square follows from the two inverses. -/
def isoOfComponents {D E : SheafPreDatum d π F φ}
    (e : D.eta ≅ E.eta) (t : D.tangent.graded ≅ E.tangent.graded)
    (hu : (latticeScalarFunctor d π (S : TopCat)).map e.hom.lattice.total ≫ E.u =
      D.u ≫ (structuralOSheafFunctor S φ).map t.hom.val.val) : D ≅ E where
  hom := ⟨e.hom, t.hom, hu⟩
  inv := {
    eta := e.inv
    tangent := t.inv
    u := by
      let ee := (FramedLatticePiSheaf.latticeFunctor ⋙ LatticePiSheaf.totalFunctor ⋙
        latticeScalarFunctor d π (S : TopCat)).mapIso e
      let tt := (GradedPiSheaf.forgetToPiSheaf ⋙ PiSheaf.forgetToModules ⋙
        structuralOSheafFunctor S φ).mapIso t
      change ee.inv ≫ D.u = E.u ≫ tt.inv
      have hh : ee.hom ≫ E.u = D.u ≫ tt.hom := hu
      calc
        _ = (ee.inv ≫ (D.u ≫ tt.hom)) ≫ tt.inv := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        _ = (ee.inv ≫ (ee.hom ≫ E.u)) ≫ tt.inv :=
          congrArg (fun k => (ee.inv ≫ k) ≫ tt.inv) hh.symm
        _ = _ := by simp only [Iso.inv_hom_id_assoc] }
  hom_inv_id := Hom.ext e.hom_inv_id t.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id t.inv_hom_id

variable (D : SheafPreDatum d π F φ)

/-- Identity pullback of the actual total u commutes with the canonical
framed-lattice and tangent identity comparisons. -/
theorem pullbackU_id :
    (latticeScalarFunctor d π (S : TopCat)).map
        D.eta.inverseImageIdIso.hom.lattice.total ≫ D.u =
      D.pullbackU (𝟙 S) ≫ (structuralOSheafFunctor S φ).map
        D.tangent.graded.pullbackIdIso.hom.val.val := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) (𝟙 (S : TopCat))
  let e := inverseImageLatticeScalarIso (𝟙 (S : TopCat)) D.eta.lattice.sheaf
  let c := inverseImageIdIso O (S : TopCat)
  let q := structuralPullbackComparison (𝟙 S) φ
  let t := (Scheme.Modules.pullbackId S).app D.tangent.graded.module
  let G := structuralOSheafFunctor S φ
  have hs := congrArg (fun k => k.hom.app D.eta.lattice.sheaf)
    (inverseImageRestrictionIso_id (algebraMap O (PiAlgebra d π)) (S : TopCat))
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hs
  have hc := congrArg (fun k => k.app D.tangent.graded.module)
    (structuralPullbackComparison_id φ)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hc
  have hn := c.hom.naturality D.u
  dsimp only [Functor.id_map] at hn
  change _ ≫ D.u = (e.inv ≫ (P.map D.u ≫ q.app D.tangent.graded.module)) ≫
    G.map t.hom
  have he : (latticeScalarFunctor d π (S : TopCat)).map
      D.eta.inverseImageIdIso.hom.lattice.total =
      e.inv ≫ c.hom.app (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact hs
  calc
    _ = (e.inv ≫ c.hom.app
        (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf)) ≫ D.u :=
      congrArg (fun k => k ≫ D.u) he
    _ = e.inv ≫ (P.map D.u ≫
        c.hom.app ((structuralOSheafFunctor S φ).obj D.tangent.graded.module)) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => e.inv ≫ k) hn.symm)
    _ = e.inv ≫ (P.map D.u ≫ (q.app D.tangent.graded.module ≫ G.map t.hom)) :=
      congrArg (fun k => e.inv ≫ (P.map D.u ≫ k)) hc.symm
    _ = _ := by simp only [Category.assoc]

/-- Composite pullback of the actual total u commutes with the canonical
framed-lattice and tangent composition comparisons. -/
theorem pullbackU_comp (f : S' ⟶ S) (g : S'' ⟶ S') :
    (latticeScalarFunctor d π (S'' : TopCat)).map
        (D.eta.inverseImageCompIso f.base g.base).hom.lattice.total ≫
          D.pullbackU (g ≫ f) =
      (D.pullback f).pullbackU g ≫
        (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)).map
          (D.tangent.graded.pullbackCompIso f g).hom.val.val := by
  let Pf := TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base
  let Pg := TopCat.Sheaf.pullback (ModuleCat.{u} O) g.base
  let Pc := TopCat.Sheaf.pullback (ModuleCat.{u} O) (g ≫ f).base
  let L := latticeScalarFunctor d π (S'' : TopCat)
  let G := structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)
  let ef := inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf
  let eg := inverseImageLatticeScalarIso g.base (D.eta.inverseImage f.base).lattice.sheaf
  let ec := inverseImageLatticeScalarIso (g ≫ f).base D.eta.lattice.sheaf
  let c := inverseImageCompIso O f.base g.base
  let cR := (inverseImageCompIso (PiAlgebra d π) f.base g.base).app D.eta.lattice.sheaf
  let qf := structuralPullbackComparison f φ
  let qg := structuralPullbackComparison g (pulledGlobalScalar f φ)
  let qc := structuralPullbackComparison (g ≫ f) φ
  let t := (Scheme.Modules.pullbackComp g f).app D.tangent.graded.module
  have hs : c.hom.app (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) ≫
      ec.hom = Pg.map ef.hom ≫ eg.hom ≫ L.map cR.hom :=
    congrArg (fun e => e.hom.app D.eta.lattice.sheaf)
      (inverseImageRestrictionIso_comp (algebraMap O (PiAlgebra d π)) f.base g.base)
  have hi : Pg.map ef.inv ≫ Pg.map ef.hom = 𝟙 _ := by
    rw [← Pg.map_comp, Iso.inv_hom_id, Pg.map_id]
  have he : L.map cR.hom ≫ ec.inv =
      eg.inv ≫ Pg.map ef.inv ≫
        c.hom.app (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) := by
    apply (cancel_mono ec.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hs, ← Category.assoc (Pg.map ef.inv), hi, Category.id_comp,
      Iso.inv_hom_id_assoc]
  have hn : Pg.map (Pf.map D.u) ≫
      c.hom.app ((structuralOSheafFunctor S φ).obj D.tangent.graded.module) =
    c.hom.app (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) ≫
      Pc.map D.u := c.hom.naturality D.u
  have hc : c.hom.app ((structuralOSheafFunctor S φ).obj D.tangent.graded.module) ≫
      qc.app D.tangent.graded.module =
    Pg.map (qf.app D.tangent.graded.module) ≫
      qg.app ((Scheme.Modules.pullback f).obj D.tangent.graded.module) ≫ G.map t.hom :=
    congrArg (fun k => k.app D.tangent.graded.module)
      (structuralPullbackComparison_comp f g φ)
  change L.map cR.hom ≫
      (ec.inv ≫ (Pc.map D.u ≫ qc.app D.tangent.graded.module)) =
    (eg.inv ≫ (Pg.map (ef.inv ≫ (Pf.map D.u ≫ qf.app D.tangent.graded.module)) ≫
      qg.app ((Scheme.Modules.pullback f).obj D.tangent.graded.module))) ≫ G.map t.hom
  calc
    _ = (L.map cR.hom ≫ ec.inv) ≫
        (Pc.map D.u ≫ qc.app D.tangent.graded.module) :=
      (Category.assoc _ _ _).symm
    _ = (eg.inv ≫ Pg.map ef.inv ≫ c.hom.app
        (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf)) ≫
          (Pc.map D.u ≫ qc.app D.tangent.graded.module) :=
      congrArg (fun k => k ≫ (Pc.map D.u ≫ qc.app D.tangent.graded.module)) he
    _ = eg.inv ≫ Pg.map ef.inv ≫
        (Pg.map (Pf.map D.u) ≫ c.hom.app
          ((structuralOSheafFunctor S φ).obj D.tangent.graded.module)) ≫
            qc.app D.tangent.graded.module := by
      simpa only [Category.assoc] using congrArg
        (fun k => eg.inv ≫ Pg.map ef.inv ≫ k ≫ qc.app D.tangent.graded.module) hn.symm
    _ = eg.inv ≫ Pg.map ef.inv ≫ Pg.map (Pf.map D.u) ≫
        (Pg.map (qf.app D.tangent.graded.module) ≫
          qg.app ((Scheme.Modules.pullback f).obj D.tangent.graded.module) ≫
            G.map t.hom) := by
      simpa only [Category.assoc] using congrArg
        (fun k => eg.inv ≫ Pg.map ef.inv ≫ Pg.map (Pf.map D.u) ≫ k) hc
    _ = _ := by simp only [Pg.map_comp, Category.assoc]

/-- Identity-base comparison preserving eta, T, u and the full rational frame. -/
def pullbackIdIso : D.pullback (𝟙 S) ≅ D :=
  isoOfComponents D.eta.inverseImageIdIso D.tangent.graded.pullbackIdIso D.pullbackU_id

/-- The identity comparison is natural for all morphisms of the four data. -/
def pullbackIdNatIso :
    pullbackFunctor (d := d) (π := π) (F := F) (φ := φ) (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun D => D.pullbackIdIso) (fun g =>
    Hom.ext (FramedLatticePiSheaf.inverseImageIdNatIso.hom.naturality g.eta)
      (GradedPiSheaf.pullbackIdNatIso.hom.naturality g.tangent))

/-- Composite-base comparison preserving eta, T, u and the full rational frame. -/
def pullbackCompIso (f : S' ⟶ S) (g : S'' ⟶ S') :
    (D.pullback f).pullback g ≅ D.pullback (g ≫ f) :=
  isoOfComponents (D.eta.inverseImageCompIso f.base g.base)
    (D.tangent.graded.pullbackCompIso f g) (D.pullbackU_comp f g)

/-- The composition comparison is natural for all morphisms of the four data. -/
def pullbackCompNatIso (f : S' ⟶ S) (g : S'' ⟶ S') :
    pullbackFunctor (d := d) (π := π) (F := F) (φ := φ) f ⋙ pullbackFunctor g ≅
      pullbackFunctor (g ≫ f) :=
  NatIso.ofComponents (fun D => D.pullbackCompIso f g) (fun h =>
    Hom.ext ((FramedLatticePiSheaf.inverseImageCompNatIso f.base g.base).hom.naturality h.eta)
      ((GradedPiSheaf.pullbackCompNatIso f g).hom.naturality h.tangent))

variable {S''' : Scheme.{u}}

/-- The actual four-data composition comparisons satisfy associativity. -/
theorem pullbackCompIso_assoc (f : S' ⟶ S) (g : S'' ⟶ S') (h : S''' ⟶ S'') :
    (pullbackFunctor h).mapIso (D.pullbackCompIso f g) ≪≫
        D.pullbackCompIso (g ≫ f) h =
      (D.pullback f).pullbackCompIso g h ≪≫ D.pullbackCompIso f (h ≫ g) := by
  apply Iso.ext
  exact Hom.ext (congrArg Iso.hom (D.eta.inverseImageCompIso_assoc f.base g.base h.base))
    (congrArg Iso.hom (D.tangent.graded.pullbackCompIso_assoc f g h))

/-- The identity on the original base is a unit for four-data pullback. -/
theorem pullbackCompIso_id_left (f : S' ⟶ S) :
    D.pullbackCompIso (𝟙 S) f =
      (pullbackFunctor f).mapIso D.pullbackIdIso := by
  apply Iso.ext
  exact Hom.ext (congrArg Iso.hom (D.eta.inverseImageCompIso_id_left f.base))
    (congrArg Iso.hom (D.tangent.graded.pullbackCompIso_id_left f))

/-- The identity on the new base is a unit for four-data pullback. -/
theorem pullbackCompIso_id_right (f : S' ⟶ S) :
    D.pullbackCompIso f (𝟙 S') = (D.pullback f).pullbackIdIso := by
  apply Iso.ext
  exact Hom.ext (congrArg Iso.hom (D.eta.inverseImageCompIso_id_right f.base))
    (congrArg Iso.hom (D.tangent.graded.pullbackCompIso_id_right f))

namespace IsoClass

/-- Identity pullback is the identity on genuine preliminary isomorphism classes. -/
@[simp]
theorem pullback_id (x : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    pullback (𝟙 S) x = x := by
  induction x using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.pullbackIdIso⟩

/-- Successive pullbacks equal composite-base pullback on preliminary classes. -/
theorem pullback_comp (f : S' ⟶ S) (g : S'' ⟶ S')
    (x : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    pullback g (pullback f x) = pullback (g ≫ f) x := by
  induction x using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.pullbackCompIso f g⟩

end IsoClass

end SheafPreDatum

end Langlands.DeligneFormalSpace
