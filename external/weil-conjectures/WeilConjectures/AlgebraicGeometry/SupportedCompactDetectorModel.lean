/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.Topology.StalkDirectSums
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # A small-Hom model for a supported compact detector

Source: Stacks Project, duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-compact-detector-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- Full faithfulness and preservation of coproducts identify the compactness comparison
with the comparison for the image object (Stacks Project, Tag 09SM). -/
private theorem compact_of_fully_faithful
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasCoproducts.{u} C] [HasCoproducts.{u} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F]
    (e : C) (h : IsCompactObject (F.obj e)) : IsCompactObject e := by
  classical
  intro I A
  let H (X : C) : (e ⟶ X) ≃+ (F.obj e ⟶ F.obj X) :=
    { (Functor.FullyFaithful.ofFullyFaithful F).homEquiv with
      map_add' := fun _ _ ↦ F.map_add }
  let d := DirectSum.congrAddEquiv (fun i ↦ H (A i))
  let s := sigmaComparison F A
  let t : (F.obj e ⟶ F.obj (∐ A)) ≃+ (F.obj e ⟶ ∐ fun i ↦ F.obj (A i)) :=
    { toEquiv := Iso.homCongr (Iso.refl _) (asIso s).symm
      map_add' := by intros; simp [Iso.homCongr, Preadditive.add_comp] }
  let b := (H (∐ A)).trans t
  let φ := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp e (Sigma.ι A i))
  let ψ := DirectSum.toAddMonoid
    (fun i ↦ Preadditive.rightComp (F.obj e) (Sigma.ι (fun i ↦ F.obj (A i)) i))
  have comm : b.toAddMonoidHom.comp φ = ψ.comp d.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    change b (φ (DirectSum.of _ i f)) = ψ (d (DirectSum.of _ i f))
    rw [show φ (DirectSum.of _ i f) = f ≫ Sigma.ι A i from
      DirectSum.toAddMonoid_of (fun j ↦ Preadditive.rightComp e (Sigma.ι A j)) i f]
    rw [show d (DirectSum.of _ i f) = DirectSum.of _ i (H (A i) f) from
      DirectSum.map_of (fun j ↦ (H (A j)).toAddMonoidHom) i f]
    rw [show ψ (DirectSum.of _ i (H (A i) f)) =
      H (A i) f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i from
      DirectSum.toAddMonoid_of _ i _]
    dsimp [b, t, H, Iso.homCongr]
    rw [Category.id_comp]
    change F.map (f ≫ Sigma.ι A i) ≫ inv s =
      F.map f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i
    rw [F.map_comp, Category.assoc, map_ι_comp_inv_sigmaComparison]
  have hb : Function.Bijective (fun x ↦ b (φ x)) := by
    have hh : (fun x ↦ b (φ x)) = (fun x ↦ ψ (d x)) :=
      funext (fun x ↦ DFunLike.congr_fun comm x)
    rw [hh]
    exact (h I (fun i ↦ F.obj (A i))).comp d.bijective
  exact ⟨fun _ _ hh ↦ hb.1 (congrArg b hh), fun f ↦ by
    obtain ⟨x, hx⟩ := hb.2 (b f)
    exact ⟨x, b.injective hx⟩⟩

/-- Shift adjunction and full faithfulness turn vanishing detection into a singleton
weak generating family (Stacks Project, Tags 09SJ and 09SN). -/
private theorem singleton_generator_of_detection
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{u} C]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.CommShift ℤ]
    (e : C) (E : D) (iso : F.obj e ≅ E)
    (h : ∀ K : C, IsZero (F.obj K) ↔ ∀ n : ℤ, Subsingleton (E⟦n⟧ ⟶ F.obj K)) :
    IsTriangulatedGeneratingFamily (fun _ : ULift.{u} Unit ↦ e) := by
  classical
  intro K hK
  have hn : ¬ ∀ n : ℤ, Subsingleton (E⟦n⟧ ⟶ F.obj K) := by
    intro hh
    have hz := (h K).2 hh
    apply hK
    rw [IsZero.iff_id_eq_zero]
    apply F.map_injective
    simpa using ((IsZero.iff_id_eq_zero _).mp hz)
  obtain ⟨n, hn⟩ := not_forall.mp hn
  have hf : ∃ f : E⟦n⟧ ⟶ F.obj K, f ≠ 0 := by
    by_contra! hh
    exact hn ⟨fun f g ↦ (hh f).trans (hh g).symm⟩
  obtain ⟨f, hf⟩ := hf
  have : (shiftEquiv D n).functor.Additive :=
    inferInstanceAs (shiftFunctor D n).Additive
  let adj := (shiftEquiv D n).toAdjunction
  let g : E ⟶ (F.obj K)⟦-n⟧ := adj.homEquiv E (F.obj K) f
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    apply (adj.homEquiv E (F.obj K)).injective
    exact hg.trans (adj.homAddEquiv E (F.obj K)).map_zero.symm
  let a : F.obj e ⟶ F.obj (K⟦-n⟧) :=
    iso.hom ≫ g ≫ (F.commShiftIso (-n)).inv.app K
  have ha : a ≠ 0 := by
    intro ha
    apply hg
    have hh := (cancel_epi iso.hom).mp
      (show iso.hom ≫ (g ≫ (F.commShiftIso (-n)).inv.app K) = iso.hom ≫ 0 by
        simpa [a] using ha)
    exact (cancel_mono ((F.commShiftIso (-n)).inv.app K)).mp (by simpa using hh)
  let b := F.preimage a
  have hb : b ≠ 0 := by
    intro hb
    apply ha
    simpa [b, hb] using (F.map_preimage a).symm
  let c := coproductUniqueIso (fun _ : ULift.{u} Unit ↦ e)
  refine ⟨-n, c.hom ≫ b, ?_⟩
  intro hh
  apply hb
  exact (cancel_epi c.hom).mp (by simpa using hh)

namespace AlgebraicGeometry

/-- Cohomology and stalk direct-sum comparisons preserve vanishing on the open set,
including the empty family (Stacks Project, Tags 08DT and 009E). -/
private theorem supported_closed_coproducts (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens) (I : Type u) :
    ObjectProperty.IsClosedUnderColimitsOfShape
    (fun K : schemeDerivedCategory Y ↦ schemeDerivedQCohProperty Y K ∧
      ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y)))
      (Discrete I) := by
  classical
  let P : ObjectProperty (schemeDerivedCategory Y) := fun K ↦
    schemeDerivedQCohProperty Y K ∧
      ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y))
  change P.IsClosedUnderColimitsOfShape (Discrete I)
  constructor
  rintro Z ⟨p⟩
  have : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts Y I
  refine ⟨(p.ofLE (fun _ h ↦ h.1)).prop, ?_⟩
  intro k y hy
  let R := moduleRings Y.toRingedSpace
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} R)
  let A := fun i : I ↦ p.diag.obj ⟨i⟩
  let K := fun i ↦ Q.objPreimage (A i)
  let e := fun i ↦ Q.objObjPreimageIso (A i)
  let c : Cofan A :=
    Cofan.mk (Q.obj (∐ K)) (fun i ↦ (e i).inv ≫ Q.map (Sigma.ι K i))
  obtain ⟨⟨hc⟩, hH⟩ := derivedAmbientDirectSums Y I A K e
  let c' := (Cocone.precompose (Discrete.natIsoFunctor (F := p.diag)).inv).obj p.cocone
  have hc' : IsColimit c' :=
    (IsColimit.precomposeInvEquiv Discrete.natIsoFunctor p.cocone).symm p.isColimit
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{u} R) k
  let M := fun i ↦ H.obj (A i)
  have hcomparison : IsIso (Sigma.desc (fun i ↦ H.map (c.inj i))) := hH k
  let iso : ∐ M ≅ H.obj Z :=
    asIso (Sigma.desc (fun i ↦ H.map (c.inj i))) ≪≫
      H.mapIso (hc.coconePointUniqueUpToIso hc')
  let S := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let si := (S.mapIso iso).addCommGroupIsoToAddEquiv
  have (i : I) : Subsingleton (↑(TopCat.Presheaf.stalk (M i).val.presheaf y)) :=
    (p.prop_diag_obj ⟨i⟩).2 k y hy
  obtain ⟨d, _⟩ := SheafOfModules.exists_stalk_directSum_linearEquiv R I M y
  have : Subsingleton (↑(TopCat.Presheaf.stalk (∐ M).val.presheaf y)) :=
    d.toEquiv.injective.subsingleton
  have : Subsingleton (S.obj (∐ M)) := by
    change Subsingleton (↑(TopCat.Presheaf.stalk (∐ M).val.presheaf y))
    infer_instance
  exact si.symm.injective.subsingleton

/-- Prepare the supported subcategory for the compact-generator theorem, without
constructing any tower or telescope.
Source: Stacks Project, duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-compact-detector-model).

Proof: Form the full subcategory of ambient complexes with quasi-coherent cohomology
and zero cohomology stalks on V. The hypothesis htri supplies its triangulated structure.
Ambient sums have sum cohomology; stalks commute with sums, so this property is closed
under sums, including the empty sum. The inclusion therefore creates these coproducts.
K-injective resolutions identify derived Hom with a quotient of the small set of chain
maps into a K-injective representative. Thus this full subcategory is locally u-small.
Take its ShrinkHoms model, with exactly the same objects and shrunk Hom sets. Transport
zero, addition, shifts, triangles and coproducts along the canonical equivalence.
Compose its inverse with the full-subcategory inclusion to obtain F. The supported
objects E and Q give e and q. Full faithfulness and agreement of coproducts identify
the compactness comparison for e with that for E in D_QCoh(Y), so e is compact.
The singleton coproduct is e. For a nonzero object, hgen gives a nonzero map from some
shift of E; the shift equivalence rewrites this as a map from E into a shift of the
object. Full faithfulness transports it to the model, proving singleton generation.
These constructions work also for E = 0: hgen then makes the supported category zero.
No choice of an arbitrary derived object is made; the model is ShrinkHoms of the stated
full subcategory and F is its canonical inverse followed by the inclusion. -/
theorem supported_compact_detector_model (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens) (E Q : schemeDerivedQCohCategory Y)
    (htri : ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory Y ↦
      schemeDerivedQCohProperty Y K ∧
        ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y))))
    (hcompact :
      letI : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
      IsCompactObject E)
    (hsupport : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y)))
    (hgen : ∀ K : schemeDerivedQCohCategory Y,
      (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K.obj).val.presheaf y))) →
      (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)))
    (hQ : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C)
      (_ : HasZeroObject C) (_ : HasShift C ℤ) (_ : Preadditive C)
      (_ : ∀ n : ℤ, (shiftFunctor C n).Additive) (_ : Pretriangulated C)
      (_ : IsTriangulated C) (_ : HasCoproducts.{u} C)
      (F : C ⥤ schemeDerivedCategory Y) (_ : F.CommShift ℤ),
      F.IsTriangulated ∧ F.Additive ∧
      (∀ I : Type u, PreservesColimitsOfShape (Discrete I) F) ∧
      (∀ K : C, schemeDerivedQCohProperty Y (F.obj K)) ∧
      ∃ e q : C, Nonempty (F.obj e ≅ E.obj) ∧ Nonempty (F.obj q ≅ Q.obj) ∧
        IsCompactObject e ∧
        IsTriangulatedGeneratingFamily (fun _ : ULift.{u} Unit ↦ e) := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u}
  let P : ObjectProperty (schemeDerivedCategory Y) := fun K ↦
    schemeDerivedQCohProperty Y K ∧
      ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor A k).obj K).val.presheaf y))
  let : P.IsTriangulated := htri
  let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
  let (I : Type u) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    supported_closed_coproducts Y V I
  let S := P.FullSubcategory
  let : HasCoproducts.{u} S := fun I ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete I) P
  let : LocallySmall.{u} S := inferInstance
  let C := ShrinkHoms S
  let eqv : S ≌ C := ShrinkHoms.equivalence.{u} S
  obtain ⟨hz, hs, hp, ha, ht, hi, hcs, hf, hg⟩ := triangulatedEquivalenceTransfer eqv
  let : HasZeroObject C := hz
  let : HasShift C ℤ := hs
  let : Preadditive C := hp
  let : ∀ n : ℤ, (shiftFunctor C n).Additive := ha
  let : Pretriangulated C := ht
  let : IsTriangulated C := hi
  let : eqv.functor.CommShift ℤ := hcs
  let : eqv.inverse.CommShift ℤ := eqv.commShiftInverse ℤ
  let : eqv.functor.IsTriangulated := hf
  let : eqv.inverse.IsTriangulated := hg
  let (I : Type u) : HasColimitsOfShape (Discrete I) C :=
    Adjunction.hasColimitsOfShape_of_equivalence eqv.inverse
  let F := eqv.inverse ⋙ P.ι
  let : F.CommShift ℤ := inferInstance
  let : F.IsTriangulated := inferInstance
  let : F.Additive := inferInstance
  let (I : Type u) : PreservesColimitsOfShape (Discrete I) F := inferInstance
  let i := ObjectProperty.ιOfLE (show P ≤ schemeDerivedQCohProperty Y from fun _ h ↦ h.1)
  let : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
  let G := eqv.inverse ⋙ i
  let : i.Additive := ⟨by intros; rfl⟩
  let : G.Additive := inferInstance
  let (I : Type u) : PreservesColimitsOfShape (Discrete I) i := by
    have : PreservesColimitsOfShape (Discrete I)
        (i ⋙ (schemeDerivedQCohProperty Y).ι) := by
      change PreservesColimitsOfShape (Discrete I) P.ι
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves i (schemeDerivedQCohProperty Y).ι
  let (I : Type u) : PreservesColimitsOfShape (Discrete I) G := inferInstance
  let eS : S := ⟨E.obj, E.property, hsupport⟩
  let qS : S := ⟨Q.obj, Q.property, hQ⟩
  let e : C := eqv.functor.obj eS
  let q : C := eqv.functor.obj qS
  have he : IsCompactObject e := compact_of_fully_faithful G e (by
    change IsCompactObject E
    exact hcompact)
  have hdetect (K : C) : IsZero (F.obj K) ↔
      ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ F.obj K) :=
    hgen (G.obj K) (eqv.inverse.obj K).property.2
  have hgenerate : IsTriangulatedGeneratingFamily (fun _ : ULift.{u} Unit ↦ e) :=
    singleton_generator_of_detection F e E.obj (Iso.refl _) hdetect
  exact ⟨C, inferInstance, hz, hs, hp, ha, ht, hi, inferInstance, F, inferInstance,
    inferInstance, inferInstance, fun I ↦ inferInstance,
    fun K ↦ (eqv.inverse.obj K).property.1, e, q, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩,
    he, hgenerate⟩

end AlgebraicGeometry
