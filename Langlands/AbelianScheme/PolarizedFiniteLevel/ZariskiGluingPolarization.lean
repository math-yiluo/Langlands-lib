import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingInput
import Langlands.AbelianScheme.PolarizedFiniteLevel.QuasiSeparatedDualWitness
import Langlands.AbelianScheme.PolarizedFiniteLevel.DatumTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingHom

/-! # Gluing the polarizations of rigid local data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

variable {P : Prerequisites.{u}} {g d n : ℕ} {S : Scheme.{u}} {J : Type*} {U : J → S.Opens}
  (hU : iSup U = ⊤) (c : ∀ W : SubOpens U, Datum P W.1.toScheme g d n)
  (hrig : ∀ (W : SubOpens U) (α : PolarizedIso (c W) (c W)), α = PolarizedIso.refl (c W))
  (θ : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1),
    PolarizedIso (c W) ((c W').pullback (S.homOfLE h)))

/-- Restriction isomorphisms are compatible with the transition maps. -/
theorem hom_restrictIso_overMap (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    hom (restrictIso hU c hrig θ W).hom ≫ (θ W W' h).overMap =
      pullback.map (gluedAbelian hU c hrig θ).X.hom W.1.ι (gluedAbelian hU c hrig θ).X.hom
        W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp [Scheme.homOfLE_ι]) ≫
        hom (restrictIso hU c hrig θ W').hom := by
  have hm : Mono (gluedι hU c hrig θ W') := inferInstance
  apply (cancel_mono (gluedι hU c hrig θ W')).mp
  have hw : (θ W W' h).overMap ≫ gluedι hU c hrig θ W' = gluedι hU c hrig θ W :=
    colimit.w (gluingData hU c hrig θ).functor (homOfLE h : W ⟶ W')
  rw [Category.assoc, hw, hom_restrictIso_gluedι, Category.assoc, hom_restrictIso_gluedι,
    ← Category.assoc, pullback.lift_fst, Category.comp_id]

section Cocycle

variable (P) {B : AbelianScheme S}

/-- Cocycle identity for the canonical dual base-change comparisons along `b` and then
`c`, against the direct comparison along `c ≫ b`. -/
theorem DualWitness.baseChangeIso_cocycle (WB : DualWitness B) {T T' : Scheme.{u}}
    (b : T' ⟶ S) (c : T ⟶ T') (Wb : DualWitness ((baseChange b).obj B))
    (Wd : DualWitness ((baseChange (c ≫ b)).obj B))
    (Wc : DualWitness ((baseChange c).obj ((baseChange b).obj B))) :
    (Wb.baseChangeIso P c Wc).hom ≫ Wd.map P Wc (baseChangeCompIso b c B).hom ≫
        (WB.baseChangeIso P (c ≫ b) Wd).inv ≫ (baseChangeCompIso b c (WB.dual P)).hom =
      (baseChange c).map (WB.baseChangeIso P b Wb).inv := by
  have h := dualAbelianBaseChangeIso_comp P.preservation P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility B
    WB.hasDual WB.geometry WB.inverseBundle WB.evaluation b c
    Wb.hasDual Wb.geometry Wb.inverseBundle Wb.evaluation
    Wd.hasDual Wd.geometry Wd.inverseBundle Wd.evaluation
    Wc.hasDual Wc.geometry Wc.inverseBundle Wc.evaluation
  change (baseChangeCompIso b c (WB.dual P)).hom ≫
      (baseChange c).map (WB.baseChangeIso P b Wb).hom ≫ (Wb.baseChangeIso P c Wc).hom =
    (WB.baseChangeIso P (c ≫ b) Wd).hom ≫ (Wd.mapIso P Wc (baseChangeCompIso b c B)).inv at h
  have h' : (baseChangeCompIso b c (WB.dual P)).hom ≫
      (baseChange c).map (WB.baseChangeIso P b Wb).hom =
      (WB.baseChangeIso P (c ≫ b) Wd).hom ≫ (Wd.mapIso P Wc (baseChangeCompIso b c B)).inv ≫
        (Wb.baseChangeIso P c Wc).inv := by
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hx : ((Wb.baseChangeIso P c Wc).hom ≫ Wd.map P Wc (baseChangeCompIso b c B).hom ≫
      (WB.baseChangeIso P (c ≫ b) Wd).inv ≫ (baseChangeCompIso b c (WB.dual P)).hom) ≫
        (baseChange c).map (WB.baseChangeIso P b Wb).hom = 𝟙 _ := by
    simp only [Category.assoc]
    rw [h']
    change (Wb.baseChangeIso P c Wc).hom ≫ (Wd.mapIso P Wc (baseChangeCompIso b c B)).hom ≫
      (WB.baseChangeIso P (c ≫ b) Wd).inv ≫ (WB.baseChangeIso P (c ≫ b) Wd).hom ≫
        (Wd.mapIso P Wc (baseChangeCompIso b c B)).inv ≫ (Wb.baseChangeIso P c Wc).inv = 𝟙 _
    simp
  calc _ = ((Wb.baseChangeIso P c Wc).hom ≫ Wd.map P Wc (baseChangeCompIso b c B).hom ≫
        (WB.baseChangeIso P (c ≫ b) Wd).inv ≫ (baseChangeCompIso b c (WB.dual P)).hom) ≫
          (baseChange c).map (WB.baseChangeIso P b Wb).hom ≫
            (baseChange c).map (WB.baseChangeIso P b Wb).inv := by
        rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.comp_id]
    _ = _ := by rw [← Category.assoc, hx, Category.id_comp]

/-- Homomorphisms of abelian schemes are determined by their underlying scheme maps. -/
theorem hom_injective' {X Y : AbelianScheme S} {f f' : X ⟶ Y} (h : hom f = hom f') :
    f = f' := by
  apply Additive.toMul.injective
  ext1
  ext1
  exact h

/-- The scheme map underlying the base change composition comparison, followed by the
first projection, is the canonical map of fibre products. -/
theorem hom_baseChangeCompIso_fst (X : AbelianScheme S) {T T' : Scheme.{u}} (b : T' ⟶ S)
    (c : T ⟶ T') :
    hom (baseChangeCompIso b c X).hom ≫ pullback.fst (pullback.snd X.X.hom b) c =
      pullback.map X.X.hom (c ≫ b) X.X.hom b (𝟙 _) c (𝟙 _) (by simp) (by simp) := by
  have hinv : hom (baseChangeCompIso b c X).inv ≫ pullback.fst X.X.hom (c ≫ b) =
      pullback.fst (pullback.snd X.X.hom b) c ≫ pullback.fst X.X.hom b :=
    GroupScheme.baseChangeCompIso_inv_fst b c X.toGrp
  have hsnd : hom (baseChangeCompIso b c X).hom ≫ pullback.snd (pullback.snd X.X.hom b) c =
      pullback.snd X.X.hom (c ≫ b) :=
    Over.w (groupHom (baseChangeCompIso b c X).hom).hom.hom
  apply pullback.hom_ext
  · rw [Category.assoc, ← hinv, ← Category.assoc, ← hom_comp, Iso.hom_inv_id, hom_id,
      Category.id_comp, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]
    exact (pullback.lift_snd _ _ _).symm

/-- Abstract form of the final step of `polarization_overlap`, with the dual abelian
scheme and its comparisons as variables. -/
theorem overlap_abstract {B D : AbelianScheme S} {T T' : Scheme.{u}} (b : T' ⟶ S)
    (c : T ⟶ T') {Db : AbelianScheme T'} {Dd Dc : AbelianScheme T}
    (βb : (baseChange b).obj D ≅ Db) (βd : (baseChange (c ≫ b)).obj D ≅ Dd)
    (βc : (baseChange c).obj Db ≅ Dc) (m : Dc ⟶ Dd)
    (hcoc : βc.hom ≫ m ≫ βd.inv ≫ (baseChangeCompIso b c D).hom = (baseChange c).map βb.inv)
    (lamb : (baseChange b).obj B ⟶ Db) :
    hom ((((baseChangeCompIso b c B).hom ≫ ((baseChange c).map lamb ≫ βc.hom) ≫ m) ≫
        βd.inv)) ≫ hom (baseChangeCompIso b c D).hom ≫
          pullback.fst ((baseChange b).obj D).X.hom c =
      (hom (baseChangeCompIso b c B).hom ≫ pullback.fst ((baseChange b).obj B).X.hom c) ≫
        hom (lamb ≫ βb.inv) := by
  have h2 := congrArg (fun f => hom f ≫ pullback.fst ((baseChange b).obj D).X.hom c) hcoc
  simp only [hom_comp, Category.assoc] at h2 ⊢
  rw [h2, hom_baseChange_map_fst c βb.inv, ← Category.assoc (hom ((baseChange c).map lamb)),
    hom_baseChange_map_fst c lamb]
  simp only [Category.assoc]

/-- **Overlap coherence for polarizations.** Let `κ` be an isomorphism
`(baseChange d) B ≅ (baseChange c) ((baseChange b) B)` over `c ≫ b = d` lying over the
canonical maps of fibre products. Suppose `κ` carries a polarization `lamd` (for the dual
witness `Wd`) to the pullback along `c` of a polarization `lamb` (for `Wb`). Then the two
polarizations, moved to the base changes of `D = WB.dual P`, are compatible with the
canonical maps of fibre products. -/
theorem polarization_overlap (WB : DualWitness B) {T T' : Scheme.{u}} (b : T' ⟶ S)
    (c : T ⟶ T') (d : T ⟶ S) (hd : c ≫ b = d) (Wb : DualWitness ((baseChange b).obj B))
    (Wd : DualWitness ((baseChange d).obj B))
    (Wc : DualWitness ((baseChange c).obj ((baseChange b).obj B)))
    (κ : (baseChange d).obj B ≅ (baseChange c).obj ((baseChange b).obj B))
    (hκ1 : hom κ.hom ≫ pullback.fst (pullback.snd B.X.hom b) c ≫ pullback.fst B.X.hom b =
      pullback.fst B.X.hom d)
    (hκ2 : hom κ.hom ≫ pullback.snd (pullback.snd B.X.hom b) c = pullback.snd B.X.hom d)
    (lamb : (baseChange b).obj B ⟶ Wb.dual P) (lamd : (baseChange d).obj B ⟶ Wd.dual P)
    (hlam : lamd = κ.hom ≫ Wb.pullbackMap P c Wc lamb ≫ Wd.map P Wc κ.hom) :
    hom (lamd ≫ (WB.baseChangeIso P d Wd).inv) ≫
        pullback.map (WB.dual P).X.hom d (WB.dual P).X.hom b (𝟙 _) c (𝟙 _)
          (by simp) (by simp [← hd]) =
      pullback.map B.X.hom d B.X.hom b (𝟙 _) c (𝟙 _) (by simp) (by simp [← hd]) ≫
        hom (lamb ≫ (WB.baseChangeIso P b Wb).inv) := by
  subst hd
  have r1 := congrArg (· ≫ pullback.fst B.X.hom b) (hom_baseChangeCompIso_fst B b c)
  have r2 := congrArg (· ≫ pullback.snd B.X.hom b) (hom_baseChangeCompIso_fst B b c)
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at r1 r2
  have hsnd0 : hom (baseChangeCompIso b c B).hom ≫ pullback.snd (pullback.snd B.X.hom b) c =
      pullback.snd B.X.hom (c ≫ b) :=
    Over.w (groupHom (baseChangeCompIso b c B).hom).hom.hom
  have hκ : κ = baseChangeCompIso b c B := by
    apply Iso.ext
    apply hom_injective'
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · exact hκ1.trans r1.symm
      · have e1 : hom κ.hom ≫ pullback.fst (pullback.snd B.X.hom b) c ≫
            pullback.snd B.X.hom b = pullback.snd B.X.hom (c ≫ b) ≫ c := by
          rw [pullback.condition, ← Category.assoc, hκ2]
        exact e1.trans r2.symm
    · exact hκ2.trans hsnd0.symm
  subst hκ
  subst hlam
  have eD := hom_baseChangeCompIso_fst (WB.dual P) b c
  have eB := hom_baseChangeCompIso_fst B b c
  rw [← eD, ← eB]
  exact overlap_abstract b c (WB.baseChangeIso P b Wb) (WB.baseChangeIso P (c ≫ b) Wd)
    (Wb.baseChangeIso P c Wc) (Wd.map P Wc (baseChangeCompIso b c B).hom)
    (DualWitness.baseChangeIso_cocycle P WB b c Wb Wd Wc) lamb

end Cocycle

section Glue

variable [QuasiSeparatedSpace S]

/-- The dual witness of the glued abelian scheme. -/
abbrev gluedDualWitness : DualWitness (gluedAbelian hU c hrig θ) :=
  DualWitness.ofQuasiSeparated (gluedAbelian hU c hrig θ)

/-- The local datum on a small open, transported to the restriction of the glued abelian
scheme. -/
def localTransport (W : SubOpens U) : Datum P W.1.toScheme g d n :=
  (c W).transport (restrictIso hU c hrig θ W)
    ((gluedDualWitness hU c hrig θ).pullback P W.1.ι)

/-- The local polarization, as a homomorphism to the restriction of the glued dual. -/
def localPolarization (W : SubOpens U) :
    (baseChange W.1.ι).obj (gluedAbelian hU c hrig θ) ⟶
      (baseChange W.1.ι).obj ((gluedDualWitness hU c hrig θ).dual P) :=
  (localTransport hU c hrig θ W).polarization ≫
    ((gluedDualWitness hU c hrig θ).baseChangeIso P W.1.ι
      ((gluedDualWitness hU c hrig θ).pullback P W.1.ι)).inv

/-- The polarized isomorphism between the transported local data on nested small opens. -/
def overlapIso (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    PolarizedIso (localTransport hU c hrig θ W)
      ((localTransport hU c hrig θ W').pullback (S.homOfLE h)) :=
  ((c W).transportIso (restrictIso hU c hrig θ W)
      ((gluedDualWitness hU c hrig θ).pullback P W.1.ι)).trans
    ((θ W W' h).trans (((c W').transportIso (restrictIso hU c hrig θ W')
      ((gluedDualWitness hU c hrig θ).pullback P W'.1.ι)).pullback (S.homOfLE h)).symm)

theorem hom_overlapIso_fst (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    hom (overlapIso hU c hrig θ W W' h).abelianIso.hom ≫
      pullback.fst (pullback.snd (gluedAbelian hU c hrig θ).X.hom W'.1.ι) (S.homOfLE h) =
      pullback.map (gluedAbelian hU c hrig θ).X.hom W.1.ι (gluedAbelian hU c hrig θ).X.hom
          W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp [Scheme.homOfLE_ι]) := by
  change (hom (restrictIso hU c hrig θ W).hom ≫ hom (θ W W' h).abelianIso.hom ≫
    hom ((baseChange (S.homOfLE h)).map (restrictIso hU c hrig θ W').inv)) ≫ _ = _
  simp only [Category.assoc]
  erw [hom_baseChange_map_fst (S.homOfLE h) (restrictIso hU c hrig θ W').inv]
  have e := hom_restrictIso_overMap hU c hrig θ W W' h
  rw [PolarizedIso.overMap] at e
  erw [← Category.assoc (hom (θ W W' h).abelianIso.hom), ← Category.assoc, e]
  rw [Category.assoc, ← hom_comp, Iso.hom_inv_id, hom_id]
  exact Category.comp_id _

theorem hom_overlapIso_fst_fst (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    hom (overlapIso hU c hrig θ W W' h).abelianIso.hom ≫
      pullback.fst (pullback.snd (gluedAbelian hU c hrig θ).X.hom W'.1.ι) (S.homOfLE h) ≫
        pullback.fst (gluedAbelian hU c hrig θ).X.hom W'.1.ι =
      pullback.fst (gluedAbelian hU c hrig θ).X.hom W.1.ι := by
  rw [← Category.assoc, hom_overlapIso_fst, pullback.lift_fst, Category.comp_id]

theorem hom_overlapIso_snd (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    hom (overlapIso hU c hrig θ W W' h).abelianIso.hom ≫
      pullback.snd (pullback.snd (gluedAbelian hU c hrig θ).X.hom W'.1.ι) (S.homOfLE h) =
      pullback.snd (gluedAbelian hU c hrig θ).X.hom W.1.ι :=
  Over.w (groupHom (overlapIso hU c hrig θ W W' h).abelianIso.hom).hom.hom

/-- The local polarizations agree on overlaps. -/
theorem localPolarization_compat (W W' : SubOpens U) (h : W.1 ≤ W'.1) :
    hom (localPolarization hU c hrig θ W) ≫
        pullback.map ((gluedDualWitness hU c hrig θ).dual P).X.hom W.1.ι
          ((gluedDualWitness hU c hrig θ).dual P).X.hom W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _)
          (by simp) (by simp [Scheme.homOfLE_ι]) =
      pullback.map (gluedAbelian hU c hrig θ).X.hom W.1.ι (gluedAbelian hU c hrig θ).X.hom
          W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp [Scheme.homOfLE_ι]) ≫
        hom (localPolarization hU c hrig θ W') :=
  polarization_overlap P (gluedDualWitness hU c hrig θ) W'.1.ι (S.homOfLE h) W.1.ι
    (Scheme.homOfLE_ι S h) _ _ _ (overlapIso hU c hrig θ W W' h).abelianIso
    (hom_overlapIso_fst_fst hU c hrig θ W W' h) (hom_overlapIso_snd hU c hrig θ W W' h)
    (localTransport hU c hrig θ W').polarization (localTransport hU c hrig θ W).polarization
    (overlapIso hU c hrig θ W W' h).polarization_eq

/-- The glued polarization of the glued abelian scheme. -/
def gluedPolarization :
    gluedAbelian hU c hrig θ ⟶ (gluedDualWitness hU c hrig θ).dual P :=
  gluedHom hU (localPolarization hU c hrig θ) (localPolarization_compat hU c hrig θ)

theorem baseChange_map_gluedPolarization (W : SubOpens U) :
    (baseChange W.1.ι).map (gluedPolarization hU c hrig θ) = localPolarization hU c hrig θ W :=
  hom_injective' (baseChange_map_gluedHom hU _ _ W)

/-- The pullback of the glued polarization to a small open is the transported local
polarization. -/
theorem pullbackMap_gluedPolarization (W : SubOpens U) :
    (gluedDualWitness hU c hrig θ).pullbackMap P W.1.ι
        ((gluedDualWitness hU c hrig θ).pullback P W.1.ι) (gluedPolarization hU c hrig θ) =
      (localTransport hU c hrig θ W).polarization := by
  unfold DualWitness.pullbackMap
  rw [baseChange_map_gluedPolarization, localPolarization, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end Glue

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
