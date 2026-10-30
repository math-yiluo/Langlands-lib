import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Proof: the noetherian affine agreement locus from the noetherian seesaw -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

section LocallyIsoOver

/-- Two module sheaves on `X` are isomorphic locally over the target of `f`: every point of `T`
has an open neighbourhood `U` such that the sheaves become isomorphic on `f ⁻¹ U`. This is the
condition appearing on the right of `NoetherianLineBundleSeesawStatement`. -/
def LocallyIsoOver {X T : Scheme.{u}} (f : X ⟶ T) (M N : X.Modules) : Prop :=
  ∀ τ : T, ∃ U : T.Opens, τ ∈ U ∧
    Nonempty (M.restrict (f ⁻¹ᵁ U).ι ≅ N.restrict (f ⁻¹ᵁ U).ι)

variable {X Y T : Scheme.{u}}

/-- Lemma A: an isomorphism over an open pulls back along any map landing in the open. -/
theorem nonempty_pullback_iso_of_restrict_iso {M N : Y.Modules} (V : Y.Opens)
    (e : M.restrict V.ι ≅ N.restrict V.ι) (a : X ⟶ Y) (ha : ∀ x, a x ∈ V) :
    Nonempty ((Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N) := by
  have hrange : Set.range a ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ha x
  let κ := IsOpenImmersion.lift V.ι a hrange
  have hκ : κ ≫ V.ι = a := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr hκ.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp κ V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback κ).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ e ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N) ≪≫
    (Scheme.Modules.pullbackComp κ V.ι).app N ≪≫
    (Scheme.Modules.pullbackCongr hκ).app N⟩

/-- Lemma B: local isomorphism over the base transports along a map over the base. -/
theorem LocallyIsoOver.of_pullback {f : Y ⟶ T} {f' : X ⟶ T} (φ : X ⟶ Y) (hφ : φ ≫ f = f')
    {M N : Y.Modules} {M' N' : X.Modules}
    (eM : M' ≅ (Scheme.Modules.pullback φ).obj M) (eN : N' ≅ (Scheme.Modules.pullback φ).obj N)
    (H : LocallyIsoOver f M N) : LocallyIsoOver f' M' N' := by
  subst hφ
  intro τ
  obtain ⟨U, hτ, ⟨e⟩⟩ := H τ
  refine ⟨U, hτ, ?_⟩
  obtain ⟨E⟩ := nonempty_pullback_iso_of_restrict_iso (f ⁻¹ᵁ U) e
    (((φ ≫ f) ⁻¹ᵁ U).ι ≫ φ) (fun x ↦ x.2)
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback _).app M' ≪≫
    (Scheme.Modules.pullback _).mapIso eM ≪≫
    (Scheme.Modules.pullbackComp _ φ).app M ≪≫ E ≪≫
    ((Scheme.Modules.pullbackComp _ φ).app N).symm ≪≫
    (Scheme.Modules.pullback _).mapIso eN.symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback _).app N').symm⟩

/-- A global isomorphism is a local isomorphism over any base. -/
theorem LocallyIsoOver.of_iso (f : X ⟶ T) {M N : X.Modules} (e : M ≅ N) :
    LocallyIsoOver f M N :=
  fun _ ↦ ⟨⊤, trivial, ⟨(Scheme.Modules.restrictFunctor _).mapIso e⟩⟩

end LocallyIsoOver

section SeesawSpace

variable {S X : Scheme.{u}} (c : X ⟶ S) {T' U : Over S} (h : T' ⟶ U)

/-- The base-change map of the relative family, with explicit fibre products. It is
definitionally `(relativeSpace c).map h`. -/
def relativeMap : pullback T'.hom c ⟶ pullback U.hom c :=
  pullback.lift (pullback.fst T'.hom c ≫ h.left) (pullback.snd T'.hom c)
    (by rw [Category.assoc, Over.w h, pullback.condition])

lemma relativeMap_fst :
    relativeMap c h ≫ pullback.fst U.hom c = pullback.fst T'.hom c ≫ h.left :=
  pullback.lift_fst _ _ _

lemma relativeMap_snd : relativeMap c h ≫ pullback.snd U.hom c = pullback.snd T'.hom c :=
  pullback.lift_snd _ _ _

/-- The member of the relative family over `T'` maps to the seesaw fibre product. -/
def toSeesawSpace :
    pullback T'.hom c ⟶ pullback (pullback.snd c U.hom) h.left :=
  pullback.lift (relativeMap c h ≫ (pullbackSymmetry c U.hom).inv)
    (pullback.fst T'.hom c) (by
      rw [Category.assoc, pullbackSymmetry_inv_comp_snd, relativeMap_fst])

/-- The seesaw fibre product maps to the member of the relative family over `T'`. -/
def fromSeesawSpace :
    pullback (pullback.snd c U.hom) h.left ⟶ pullback T'.hom c :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst c U.hom) (by
    rw [← Over.w h, ← pullback.condition_assoc, Category.assoc,
      pullback.condition (f := c) (g := U.hom)])

lemma toSeesawSpace_snd :
    toSeesawSpace c h ≫ pullback.snd _ _ = pullback.fst T'.hom c :=
  pullback.lift_snd _ _ _

lemma toSeesawSpace_fst :
    toSeesawSpace c h ≫ pullback.fst _ _ ≫ (pullbackSymmetry c U.hom).hom =
      relativeMap c h := by
  rw [toSeesawSpace, pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

lemma fromSeesawSpace_fst :
    fromSeesawSpace c h ≫ pullback.fst T'.hom c = pullback.snd _ _ :=
  pullback.lift_fst _ _ _

lemma fromSeesawSpace_snd :
    fromSeesawSpace c h ≫ pullback.snd T'.hom c = pullback.fst _ _ ≫ pullback.fst c U.hom :=
  pullback.lift_snd _ _ _

lemma fromSeesawSpace_map :
    fromSeesawSpace c h ≫ relativeMap c h =
      pullback.fst _ _ ≫ (pullbackSymmetry c U.hom).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeMap_fst, reassoc_of% fromSeesawSpace_fst, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullback.condition]
  · rw [Category.assoc, relativeMap_snd, fromSeesawSpace_snd, Category.assoc,
      pullbackSymmetry_hom_comp_snd]

/-- The seesaw locus condition is the local-isomorphism condition on the relative family. -/
theorem locallyIsoOver_seesaw_iff (M N : ((relativeSpace c).obj U).Modules) :
    LocallyIsoOver (pullback.snd (pullback.snd c U.hom) h.left)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c U.hom) h.left)).obj
          ((Scheme.Modules.pullback (pullbackSymmetry c U.hom).hom).obj M))
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c U.hom) h.left)).obj
          ((Scheme.Modules.pullback (pullbackSymmetry c U.hom).hom).obj N)) ↔
      LocallyIsoOver ((relativeProjection c).app T')
        ((Scheme.Modules.pullback ((relativeSpace c).map h)).obj M)
        ((Scheme.Modules.pullback ((relativeSpace c).map h)).obj N) := by
  let e₁ := fun M : ((relativeSpace c).obj U).Modules ↦
    Langlands.AbelianScheme.MumfordPicardZero.pullbackCompIso _ _ _
      (toSeesawSpace_fst c h) M ≪≫
      (Scheme.Modules.pullback (toSeesawSpace c h)).mapIso
        ((Scheme.Modules.pullbackComp _ _).app M).symm
  let e₂ := fun M : ((relativeSpace c).obj U).Modules ↦
    (Scheme.Modules.pullbackComp _ _).app M ≪≫
      Langlands.AbelianScheme.MumfordPicardZero.pullbackCompIso _ _ _
        (fromSeesawSpace_map c h) M
  exact ⟨LocallyIsoOver.of_pullback (toSeesawSpace c h) (toSeesawSpace_snd c h) (e₁ M) (e₁ N),
    LocallyIsoOver.of_pullback (fromSeesawSpace c h) (fromSeesawSpace_fst c h)
      (e₂ M) (e₂ N)⟩

end SeesawSpace

section Classes

open Langlands.AbelianScheme

variable (separated : RigidifiedClassesZariskiSeparatedStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include separated in
/-- Two rigidified classes agree after pullback along `h` exactly when the underlying
pulled-back sheaves are isomorphic locally over the test scheme. -/
theorem classesPullback_mk_eq_iff {T U : Over S} (h : T ⟶ U) (L L' : RigidifiedFamily A U) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h ⟦L⟧ =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
          ⟦L'⟧ ↔
      LocallyIsoOver ((relativeProjection A.X.hom).app T)
        ((Scheme.Modules.pullback ((relativeSpace A.X.hom).map h)).obj L.obj.carrier)
        ((Scheme.Modules.pullback ((relativeSpace A.X.hom).map h)).obj L'.obj.carrier) := by
  constructor
  · intro H
    obtain ⟨e⟩ := Quotient.exact H
    exact LocallyIsoOver.of_iso _
      ((RigidifiedLineBundle.forget _ ⋙ LineBundle.forget _).mapIso e)
  · intro H
    choose V hV e using H
    have hcover : TopologicalSpace.IsOpenCover V := by
      refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun τ _ ↦ ?_)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨τ, hV τ⟩
    apply separated S A T (T.left.openCoverOfIsOpenCover V hcover)
    intro τ
    let k : Over.mk ((V τ).ι ≫ T.hom) ⟶ T := Over.homMk (V τ).ι
    have ha : ∀ x, (relativeSpace A.X.hom).map k x ∈
        (relativeProjection A.X.hom).app T ⁻¹ᵁ V τ := by
      intro x
      show ((relativeSpace A.X.hom).map k ≫ (relativeProjection A.X.hom).app T) x ∈ V τ
      rw [(relativeProjection A.X.hom).naturality k]
      exact ((relativeProjection A.X.hom).app _ x).2
    obtain ⟨E⟩ := nonempty_pullback_iso_of_restrict_iso _ (e τ).some _ ha
    exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
      ((relativeProjection A.X.hom).app _)
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) _)
      (ObjectProperty.isoMk _ E))

end Classes

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency.types false in
/-- The noetherian affine agreement locus follows from the noetherian seesaw, Zariski
separatedness of rigidified classes, and geometric integrality of smooth geometrically
connected schemes over fields. -/
theorem rigidifiedClassesEqualizerClosedNoetherianAffine_of_seesaw :
    RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement.{u} := by
  intro seesaw separated integrality R _ A q r
  induction q using Quotient.inductionOn with | h L => ?_
  induction r using Quotient.inductionOn with | h L' => ?_
  have : GeometricallyIntegral A.X.hom := by
    rw [GeometricallyIntegral.iff_geometricallyIntegral_fiber]
    intro s
    have hs : Smooth (A.X.hom.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd _ _ A.smooth
    have hc : GeometricallyConnected (A.X.hom.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd _ _ A.geometricallyConnected
    exact integrality _ _ _ hs hc
  have hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective
        (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop := by
    intro B _ _
    have := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
      (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      inferInstance inferInstance inferInstance ⊤
    exact ConcreteCategory.bijective_of_isIso
      ((pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B)))).app ⊤)
  obtain ⟨Z, ι, hι, hZ⟩ := seesaw (R := R) (T := Spec R) A.X.hom hH0 (Over.mk (𝟙 (Spec R))).hom
    ((Scheme.Modules.pullback (pullbackSymmetry A.X.hom (Over.mk (𝟙 (Spec R))).hom).hom).obj
      L.obj.carrier)
    ((Scheme.Modules.pullback (pullbackSymmetry A.X.hom (Over.mk (𝟙 (Spec R))).hom).hom).obj
      L'.obj.carrier)
    (L.property.pullback _) (L'.property.pullback _)
  exact ⟨Z, ι, hι, fun T' h ↦ (hZ h.left).trans ((locallyIsoOver_seesaw_iff A.X.hom h _ _).trans
    (classesPullback_mk_eq_iff separated A h L L').symm)⟩

end Langlands.AbelianScheme
