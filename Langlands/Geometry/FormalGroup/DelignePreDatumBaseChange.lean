import Langlands.Geometry.FormalGroup.DeligneStructuralBaseChange
import Langlands.Geometry.ModuleSheafLocalSpan

/-! # Actual base change of Deligne's four preliminary sheaf data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {S S' : Scheme.{u}}
  {d : ℕ} [NeZero d] {π : O} {F : Type u} [Field F] [Algebra O F]
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- The actual pulled total map, on the constructed inverse-image lattice. -/
def pullbackU :
    latticeScalarSheaf d π (S' : TopCat) (D.eta.inverseImage f.base).lattice.sheaf ⟶
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).obj
        ((D.tangent.pullback f).graded.module) :=
  (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).inv ≫
    D.inverseImageU f φ

/-- The actual pulled homogeneous map, into the constructed range component. -/
def pullbackUComponent (i : ZMod d) :
    (D.eta.inverseImage f.base).lattice.component i ⟶
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).obj
        ((D.tangent.pullback f).graded.componentSheaf i) :=
  D.inverseImageUComponent f φ i ≫
    (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
      (D.tangent.graded.pullbackComponentIso f i).hom

/-- The constructed pulled total map commutes with the actual Pi operators. -/
theorem pullbackU_pi :
    latticePi d π (S' : TopCat) (D.eta.inverseImage f.base).lattice.sheaf ≫
        D.pullbackU f =
      D.pullbackU f ≫
        (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
          (D.tangent.pullback f).graded.pi := by
  let e := inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf
  have h := inverseImageLatticeScalarIso_pi f.base D.eta.lattice.sheaf
  change _ ≫ e.hom = e.hom ≫ _ at h
  have hi :
      latticePi d π (S' : TopCat) (D.eta.inverseImage f.base).lattice.sheaf ≫ e.inv =
        e.inv ≫ (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map
          (latticePi d π (S : TopCat) D.eta.lattice.sheaf) := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg (fun k => e.inv ≫ k) h.symm
    simp only [Iso.inv_hom_id_assoc] at hh
    exact hh
  change _ ≫ (e.inv ≫ D.inverseImageU f φ) =
    (e.inv ≫ D.inverseImageU f φ) ≫ _
  rw [← Category.assoc, hi, Category.assoc, D.inverseImageU_pi, ← Category.assoc]
  rfl

/-- The pulled component maps are restrictions of the same pulled total map. -/
theorem pullbackUComponent_inclusion (i : ZMod d) :
    D.pullbackUComponent f i ≫
        (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
          ((D.tangent.pullback f).graded.componentInclusion i) =
      (D.eta.inverseImage f.base).lattice.inclusion i ≫ D.pullbackU f := by
  let G := structuralOSheafFunctor S' (pulledGlobalScalar f φ)
  have h : (D.tangent.graded.pullbackComponentIso f i).hom ≫
      (D.tangent.pullback f).graded.componentInclusion i =
        (Scheme.Modules.pullback f).map (D.tangent.graded.componentInclusion i) :=
    splitRangeIso_hom_inclusion
      (D.tangent.graded.pullbackInclusion f i)
      (D.tangent.graded.pullbackProjection f i)
      (D.tangent.graded.pullbackInclusion_projection f i)
  change (D.inverseImageUComponent f φ i ≫ G.map _) ≫ G.map _ = _
  rw [Category.assoc, ← G.map_comp]
  calc
    _ = D.inverseImageUComponent f φ i ≫
        G.map ((Scheme.Modules.pullback f).map (D.tangent.graded.componentInclusion i)) :=
      congrArg (fun k => D.inverseImageUComponent f φ i ≫ G.map k) h
    _ = (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map
        (D.eta.lattice.inclusion i) ≫ D.inverseImageU f φ :=
      D.inverseImageUComponent_inclusion f φ i
    _ = _ := by
      change _ = (_ ≫ (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom) ≫
        ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).inv ≫ _)
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Sectionwise structural span of the actual pulled total map. -/
def pullbackSpan : ((D.tangent.pullback f).graded.module).val.Submodule where
  obj U := Submodule.span (S'.ringCatSheaf.obj.obj U)
    (Set.range (fun e : (latticeScalarSheaf d π (S' : TopCat)
        (D.eta.inverseImage f.base).lattice.sheaf).obj.obj U =>
      (show (D.tangent.pullback f).graded.module.val.obj U from
        (D.pullbackU f).hom.app U e)))
  map {U V} g := by
    intro t ht
    change (D.tangent.pullback f).graded.module.val.map g t ∈
      Submodule.span (S'.ringCatSheaf.obj.obj V)
        (Set.range (fun e : (latticeScalarSheaf d π (S' : TopCat)
            (D.eta.inverseImage f.base).lattice.sheaf).obj.obj V =>
          (show (D.tangent.pullback f).graded.module.val.obj V from
            (D.pullbackU f).hom.app V e)))
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨(latticeScalarSheaf d π (S' : TopCat)
        (D.eta.inverseImage f.base).lattice.sheaf).obj.map g e, ?_⟩
      exact congrArg (fun k => k e) ((D.pullbackU f).hom.naturality g)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [PresheafOfModules.map_smul]
      exact Submodule.smul_mem _ _ ih

/-- The actual structural unit of u factors through the pulled total map. -/
theorem pullbackU_unit :
    D.u ≫ (structuralPullbackUnit f φ).app D.tangent.graded.module =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base).unit.app
          (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base).map
          ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom ≫
            D.pullbackU f) := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base
  let P := TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base
  have hc := structuralPullbackComparison_unit f φ D.tangent.graded.module
  change A.unit.app _ ≫ P.map _ = (structuralPullbackUnit f φ).app _ at hc
  have hn := A.unit.naturality D.u
  change D.u ≫ A.unit.app _ = A.unit.app _ ≫
    P.map ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map D.u) at hn
  have he : (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom ≫
      D.pullbackU f = D.inverseImageU f φ := by
    change _ ≫ ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).inv ≫ _) = _
    simp only [Iso.hom_inv_id_assoc]
  calc
    _ = D.u ≫ (A.unit.app _ ≫ P.map
        ((structuralPullbackComparison f φ).app D.tangent.graded.module)) :=
      congrArg (fun k => D.u ≫ k) hc.symm
    _ = (D.u ≫ A.unit.app _) ≫ P.map
        ((structuralPullbackComparison f φ).app D.tangent.graded.module) :=
      (Category.assoc _ _ _).symm
    _ = (A.unit.app _ ≫ P.map
        ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map D.u)) ≫
          P.map ((structuralPullbackComparison f φ).app D.tangent.graded.module) :=
      congrArg (fun k => k ≫ P.map
        ((structuralPullbackComparison f φ).app D.tangent.graded.module)) hn
    _ = A.unit.app _ ≫ P.map (D.inverseImageU f φ) := by
      rw [Category.assoc, ← P.map_comp]
      rfl
    _ = _ := congrArg (fun k => A.unit.app _ ≫ P.map k) he.symm

/-- The structural unit takes each original span into the pulled span. -/
theorem unit_mem_pullbackSpan (U : S.Opens)
    (t : D.tangent.graded.module.val.obj (.op U))
    (ht : t ∈ Submodule.span (S.ringCatSheaf.obj.obj (.op U))
      (Set.range (fun e : (latticeScalarSheaf d π (S : TopCat)
          D.eta.lattice.sheaf).obj.obj (.op U) =>
        (show D.tangent.graded.module.val.obj (.op U) from D.u.hom.app (.op U) e)))) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      D.tangent.graded.module).val.app (.op U) t ∈
        (D.pullbackSpan f).obj (.op (f ⁻¹ᵁ U)) := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨(inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom.app
      (.op (f ⁻¹ᵁ U))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base).unit.app
          (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf)).hom.app (.op U) e), ?_⟩
    exact (congrArg (fun k => k.hom.app (.op U) e) (D.pullbackU_unit f)).symm
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ ((f.app U).hom a) ih

/-- Sections locally spanned by the actual pulled total map, as a genuine subsheaf. -/
def pullbackLocalSpan : ((D.tangent.pullback f).graded.module).Submodule :=
  ModuleSheaf.localSaturation (D.pullbackSpan f)

/-- Original local generation makes the actual structural unit land in that subsheaf. -/
theorem unit_mem_pullbackLocalSpan (U : S.Opens)
    (t : D.tangent.graded.module.val.obj (.op U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      D.tangent.graded.module).val.app (.op U) t ∈
        (D.pullbackLocalSpan f).toSubmodule.obj (.op (f ⁻¹ᵁ U)) := by
  apply (ModuleSheaf.mem_localSaturation_iff (D.pullbackSpan f) (f ⁻¹ᵁ U) _).mpr
  intro x hx
  obtain ⟨V, hVU, hxV, htV⟩ := D.locallyGenerates U t (f.base x) hx
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun y hy => hVU hy
  refine ⟨f ⁻¹ᵁ V, hpre, hxV, ?_⟩
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      D.tangent.graded.module).val (homOfLE hVU).op t
  have hm := D.unit_mem_pullbackSpan f V
    (D.tangent.graded.module.val.map (homOfLE hVU).op t) htV
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      D.tangent.graded.module).val.app (.op V)
        (D.tangent.graded.module.val.map (homOfLE hVU).op t) =
    (D.tangent.pullback f).graded.module.val.map (homOfLE hpre).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        D.tangent.graded.module).val.app (.op U) t) at hn
  exact hn ▸ hm

/-- Factor the actual structural unit through the locally spanned subsheaf. -/
def unitToPullbackLocalSpan : D.tangent.graded.module ⟶
    (Scheme.Modules.pushforward f).obj (D.pullbackLocalSpan f).toSheafOfModules := by
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro U
    refine { hom' := {
      toFun := fun t =>
        ⟨((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          D.tangent.graded.module).val.app U t,
            D.unit_mem_pullbackLocalSpan f U.unop t⟩
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_smul' := fun a x => Subtype.ext
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          D.tangent.graded.module).val.app U).hom.map_smul a x) } }
  · intro U V g
    ext t
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        D.tangent.graded.module).val g t

/-- Including the factored unit recovers the actual pullback adjunction unit. -/
theorem unitToPullbackLocalSpan_inclusion :
    D.unitToPullbackLocalSpan f ≫
      (Scheme.Modules.pushforward f).map (D.pullbackLocalSpan f).ι =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          D.tangent.graded.module := by
  apply SheafOfModules.hom_ext
  ext U t
  rfl

/-- Transpose the factored unit by the actual structural pullback adjunction. -/
def pullbackToLocalSpan : (D.tangent.pullback f).graded.module ⟶
    (D.pullbackLocalSpan f).toSheafOfModules :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (D.unitToPullbackLocalSpan f)

/-- The transpose followed by inclusion is the identity on the actual pullback. -/
theorem pullbackToLocalSpan_inclusion :
    D.pullbackToLocalSpan f ≫ (D.pullbackLocalSpan f).ι =
      𝟙 (D.tangent.pullback f).graded.module := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [pullbackToLocalSpan, Equiv.apply_symm_apply]
  calc
    _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        D.tangent.graded.module := D.unitToPullbackLocalSpan_inclusion f
    _ = _ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_id
      D.tangent.graded.module).symm

/-- Every pulled section belongs to the subsheaf locally spanned by pulled u. -/
theorem mem_pullbackLocalSpan (U : S'.Opens)
    (t : (D.tangent.pullback f).graded.module.val.obj (.op U)) :
    t ∈ (D.pullbackLocalSpan f).toSubmodule.obj (.op U) := by
  have h := congrArg (fun k => k.val.app (.op U) t)
    (D.pullbackToLocalSpan_inclusion f)
  change ((D.pullbackToLocalSpan f).val.app (.op U) t).val = t at h
  exact h ▸ ((D.pullbackToLocalSpan f).val.app (.op U) t).property

/-- Local generation is derived for the constructed pulled maps. -/
theorem pullback_locallyGenerates (U : S'.Opens)
    (t : (D.tangent.pullback f).graded.module.val.obj (.op U))
    (x : S') (hx : x ∈ U) :
    ∃ (V : S'.Opens) (hVU : V ≤ U), x ∈ V ∧
      (D.tangent.pullback f).graded.module.val.map (homOfLE hVU).op t ∈
        Submodule.span (S'.ringCatSheaf.obj.obj (.op V))
          (Set.range (fun e : (latticeScalarSheaf d π (S' : TopCat)
              (D.eta.inverseImage f.base).lattice.sheaf).obj.obj (.op V) =>
            (show (D.tangent.pullback f).graded.module.val.obj (.op V) from
              (D.pullbackU f).hom.app (.op V) e))) :=
  (ModuleSheaf.mem_localSaturation_iff (D.pullbackSpan f) U t).mp
    (D.mem_pullbackLocalSpan f U t) x hx

/-- Actual base change of the four preliminary data, including local generation. -/
def pullback : SheafPreDatum d π F (pulledGlobalScalar f φ) where
  eta := D.eta.inverseImage f.base
  tangent := D.tangent.pullback f
  u := D.pullbackU f
  uPi := D.pullbackU_pi f
  uComponent := D.pullbackUComponent f
  uComponent_inclusion := D.pullbackUComponent_inclusion f
  locallyGenerates := D.pullback_locallyGenerates f

end SheafPreDatum

end Langlands.DeligneFormalSpace
