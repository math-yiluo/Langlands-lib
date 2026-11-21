import Langlands.GroupScheme.Torus.TorusGraphSchemeQuotient
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.GroupScheme.Torus.CentralizerQuotient

/-! # The group quotient obtained using the smooth graph relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusGraphQuotient

open Langlands.CategoryTheory.GroupObjectDescent
open SelfCentralizingConjugacyClosedEmbeddingReduction (exists_factor_of_fppf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G L : GroupScheme S} {T D : CommGroupScheme S}

section Pullback

variable {Q : Over S} (p : G.X ⊗ D.X ⟶ Q)

/-- The map `G ⟶ Q` obtained by inserting the unit of `D`. -/
def quotientMap : G.X ⟶ Q := lift (𝟙 G.X) (1 : G.X ⟶ D.X) ≫ p

/-- The map `D ⟶ Q` obtained by inserting the unit of `G`. -/
def torusMap : D.X ⟶ Q := lift (1 : D.X ⟶ G.X) (𝟙 D.X) ≫ p

variable (ρ : G ⟶ L) (e : D.toGrp ⟶ L) (j : Q ⟶ L.X) (hj : p ≫ j = productMap ρ e)

include hj in
@[reassoc]
theorem quotientMap_fac : quotientMap p ≫ j = ρ.hom.hom := by
  rw [quotientMap, Category.assoc, hj, comp_productMap]
  simp only [lift_fst_assoc, Category.id_comp, lift_snd_assoc, MonObj.one_comp, mul_one]

include hj in
@[reassoc]
theorem torusMap_fac : torusMap p ≫ j = e.hom.hom := by
  rw [torusMap, Category.assoc, hj, comp_productMap]
  simp only [lift_fst_assoc, MonObj.one_comp, lift_snd_assoc, Category.id_comp, one_mul]

/-- The action map `(g, τ) ↦ g t(τ)` over the base. -/
def graphAction (t : T.toGrp ⟶ G) : G.X ⊗ T.X ⟶ G.X :=
  fst G.X T.X * (snd G.X T.X ≫ t.hom.hom)

@[reassoc]
theorem comp_graphAction (t : T.toGrp ⟶ G) {U : Over S} (a : U ⟶ G.X ⊗ T.X) :
    a ≫ graphAction t = (a ≫ fst G.X T.X) * (a ≫ snd G.X T.X ≫ t.hom.hom) := by
  simp only [graphAction, MonObj.comp_mul]

variable (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) [Mono j]
variable (hπe : π ≫ e = t ≫ ρ)

include hj hπe in
private theorem graphAction_comm :
    (𝟙 G.X ⊗ₘ π.hom.hom) ≫ p = graphAction t ≫ quotientMap p := by
  have hf : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun h => h.hom.hom) hπe
  apply (cancel_mono j).mp
  rw [Category.assoc, hj, Category.assoc, quotientMap_fac p ρ e j hj, comp_productMap]
  simp only [tensorHom_fst_assoc, Category.id_comp, tensorHom_snd_assoc, graphAction,
    MonObj.mul_comp, Category.assoc, hf]

variable [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
  [LocallyOfFinitePresentation π.hom.hom.left]
variable (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
variable (hcent : (torusCentralizer t).IsRepresentedBy t) (he : Mono e.hom.hom)

include hj hπe hρ hcent he in
/-- The pullback of the induced `G ⟶ Q` along `G × D ⟶ Q` is
`G × T ⟶ G × D`, induced by the identity on `G` and `π` on `T`. -/
theorem quotientMap_isPullback :
    IsPullback (𝟙 G.X ⊗ₘ π.hom.hom) (graphAction t) p (quotientMap p) := by
  let : Mono t.hom.hom := hcent.1
  have H := graphAction_comm p ρ e j hj t π hπe
  refine ⟨⟨H⟩, ⟨PullbackCone.isLimitAux' (PullbackCone.mk _ _ H) ?_⟩⟩
  intro c
  let g := c.fst ≫ fst G.X D.X
  let d := c.fst ≫ snd G.X D.X
  have hc : c.snd ≫ ρ.hom.hom = (g ≫ ρ.hom.hom) * (d ≫ e.hom.hom) := by
    have Hc := congrArg (fun f => f ≫ j) c.condition.symm
    rw [Category.assoc, quotientMap_fac p ρ e j hj, Category.assoc, hj, comp_productMap] at Hc
    exact Hc
  have hy : (g⁻¹ * c.snd) ≫ ρ.hom.hom = d ≫ e.hom.hom := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hc, inv_mul_cancel_left]
  have hex := exists_graph_coordinate ρ t π e hρ hcent he hπe (g⁻¹ * c.snd) d hy
  let τ := Classical.choose hex
  have hτt : τ ≫ t.hom.hom = g⁻¹ * c.snd := (Classical.choose_spec hex).1
  have hτπ : τ ≫ π.hom.hom = d := (Classical.choose_spec hex).2
  refine ⟨lift g τ, ?_, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [PullbackCone.mk_fst, Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
      rfl
    · simp only [PullbackCone.mk_fst, Category.assoc, tensorHom_snd, lift_snd_assoc]
      exact hτπ
  · change lift g τ ≫ graphAction t = c.snd
    rw [comp_graphAction, lift_fst, lift_snd_assoc, hτt, mul_inv_cancel_left]
  · intro a ha hb
    change a ≫ (𝟙 G.X ⊗ₘ π.hom.hom) = c.fst at ha
    change a ≫ graphAction t = c.snd at hb
    have hag : a ≫ fst G.X T.X = g := by
      have Hc := congrArg (fun z => z ≫ fst G.X D.X) ha
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using Hc
    apply CartesianMonoidalCategory.hom_ext
    · rwa [lift_fst]
    · rw [lift_snd]
      apply (cancel_mono t.hom.hom).mp
      rw [Category.assoc, hτt]
      rw [comp_graphAction, hag] at hb
      rw [← hb, inv_mul_cancel_left]

private theorem id_tensor_fppf (X : Over S) {Y Z : Over S} (a : Y ⟶ Z)
    [Flat a.left] [Surjective a.left] [LocallyOfFinitePresentation a.left] :
    Flat (𝟙 X ⊗ₘ a).left ∧ Surjective (𝟙 X ⊗ₘ a).left ∧
      LocallyOfFinitePresentation (𝟙 X ⊗ₘ a).left :=
  MorphismProperty.pullbackMap
    (P := @Flat ⊓ (@Surjective ⊓ @LocallyOfFinitePresentation))
    ⟨inferInstance, inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance, inferInstance⟩
    (Over.w (𝟙 X)).symm (Over.w a).symm

include hj hπe hρ hcent he in
/-- The map from `G` is fppf by checking it after the smooth quasi-compact surjection `p`. -/
theorem quotientMap_fppf [Smooth p.left] [Surjective p.left] [QuasiCompact p.left] :
    Flat (quotientMap p).left ∧ Surjective (quotientMap p).left ∧
      LocallyOfFinitePresentation (quotientMap p).left := by
  have hpb := (quotientMap_isPullback p ρ e j hj t π hπe hρ hcent he).map (Over.forget S)
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p.left :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨hflat, hsurj, hlfp⟩ := id_tensor_fppf G.X π.hom.hom
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hpb hp hflat,
    MorphismProperty.of_isPullback_of_descendsAlong hpb hp hsurj,
    MorphismProperty.of_isPullback_of_descendsAlong hpb hp hlfp⟩

end Pullback

/-- The group-scheme factorization of a homomorphism constructed with the graph relation.
It includes a smooth cover by the product, as well as the fppf group projection. -/
structure GroupFactorization (ρ : G ⟶ L) (e : D.toGrp ⟶ L) where
  quotient : GroupScheme S
  projection : G ⟶ quotient
  embedding : quotient ⟶ L
  torus : D.toGrp ⟶ quotient
  smoothCover : G.X ⊗ D.X ⟶ quotient.X
  projection_fac : projection ≫ embedding = ρ
  torus_fac : torus ≫ embedding = e
  cover_fac : smoothCover ≫ embedding.hom.hom = productMap ρ e
  mono_embedding : Mono embedding.hom.hom.left
  flat_projection : Flat projection.hom.hom.left
  surjective_projection : Surjective projection.hom.hom.left
  lfp_projection : LocallyOfFinitePresentation projection.hom.hom.left
  smooth_cover : Smooth smoothCover.left
  surjective_cover : Surjective smoothCover.left
  smooth_quotient : Smooth quotient.X.hom
  separated_quotient : IsSeparated quotient.X.hom
  quasiCompact_quotient : QuasiCompact quotient.X.hom

section Group

variable (ρ : G ⟶ L) (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) (e : D.toGrp ⟶ L)
variable [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
  [LocallyOfFinitePresentation π.hom.hom.left]
variable [Smooth G.X.hom] [QuasiCompact G.X.hom] [Smooth D.X.hom] [QuasiCompact D.X.hom]
variable [IsSeparated L.X.hom]
variable (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
variable (hcent : (torusCentralizer t).IsRepresentedBy t) (he : Mono e.hom.hom)
variable (hπe : π ≫ e = t ≫ ρ) (hT : Smooth T.X.hom)

include hρ hcent he hπe hT in
/-- The quotient group is obtained by descending multiplication and inverse along the
fppf projection from `G`, then restricting the operations of `L` along the monomorphism. -/
theorem nonempty_groupFactorization : Nonempty (GroupFactorization ρ e) := by
  let X := graphSchemeQuotient ρ t π e hρ hcent he hπe inferInstance inferInstance hT
  let Q := X.scheme
  let p : G.X ⊗ D.X ⟶ Q := X.projection
  let j : Q ⟶ L.X := X.embedding
  have hj : p ≫ j = productMap ρ e := X.fac
  have hmono : Mono j.left := X.mono_embedding
  let : Mono j := Over.mono_of_mono_left j
  have hp : Smooth p.left := X.smooth_projection
  have hps : Surjective p.left := X.surjective_projection
  have hQsep : IsSeparated Q.hom := by rw [← Over.w j]; infer_instance
  have hSrcqc : QuasiCompact (G.X ⊗ D.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hSrcsm : Smooth (G.X ⊗ D.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hpqc : QuasiCompact (p.left ≫ Q.hom) := by rw [Over.w p]; exact hSrcqc
  have hpsm : Smooth (p.left ≫ Q.hom) := by rw [Over.w p]; exact hSrcsm
  have : QuasiCompact p.left := QuasiCompact.of_comp p.left Q.hom
  have hQqc := TorusCentralizerQuotient.quasiCompact_of_surjective_comp p.left Q.hom
  have hQsm := Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp p.left Q.hom
  let q := quotientMap p
  let r := torusMap p
  have hq : q ≫ j = ρ.hom.hom := quotientMap_fac p ρ e j hj
  have hr : r ≫ j = e.hom.hom := torusMap_fac p ρ e j hj
  obtain ⟨hqf, hqs, hql⟩ : Flat q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left :=
    quotientMap_fppf p ρ e j hj t π hπe hρ hcent he
  have hprod : (@Flat ⊓ @Surjective ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (q ⊗ₘ q).left :=
    MorphismProperty.pullbackMap ⟨⟨hqf, hqs⟩, hql⟩ ⟨⟨hqf, hqs⟩, hql⟩
      (Over.w q).symm (Over.w q).symm
  have : Flat (q ⊗ₘ q).left := hprod.1.1
  have : Surjective (q ⊗ₘ q).left := hprod.1.2
  have : LocallyOfFinitePresentation (q ⊗ₘ q).left := hprod.2
  let ηQ := η[G.X] ≫ q
  have hηQ : ηQ ≫ j = η[L.X] := by rw [show ηQ = η[G.X] ≫ q from rfl,
    Category.assoc, hq, IsMonHom.one_hom]
  obtain ⟨μQ, hμQ⟩ := exists_factor_of_fppf (q ⊗ₘ q) j ((j ⊗ₘ j) ≫ μ[L.X])
    (μ[G.X] ≫ q) (by
      rw [Category.assoc, hq, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hq])
  obtain ⟨ιQ, hιQ⟩ := exists_factor_of_fppf q j (j ≫ ι[L.X]) (ι[G.X] ≫ q) (by
    rw [Category.assoc, ← Category.assoc q j, hq, GrpObj.inv_hom ρ.hom.hom])
  let : GrpObj Q := grpObjOfMono j ηQ μQ ιQ hηQ hμQ hιQ
  let : IsMonHom j := isMonHom_grpObjOfMono j ηQ μQ ιQ hηQ hμQ hιQ
  have isMonHom_of_comp (A : GroupScheme S) (a : A.X ⟶ Q) (b : A ⟶ L)
      (hab : a ≫ j = b.hom.hom) : IsMonHom a := by
    constructor
    · apply (cancel_mono j).mp
      rw [Category.assoc, hab, IsMonHom.one_hom, IsMonHom.one_hom]
    · apply (cancel_mono j).mp
      rw [Category.assoc, hab, IsMonHom.mul_hom b.hom.hom, Category.assoc,
        IsMonHom.mul_hom j, tensorHom_comp_tensorHom_assoc, hab]
  let : IsMonHom q := isMonHom_of_comp G q ρ hq
  let : IsMonHom r := isMonHom_of_comp D.toGrp r e hr
  let Qg : GroupScheme S := Grp.mk Q
  let qg : G ⟶ Qg := Grp.homMk q
  let jg : Qg ⟶ L := Grp.homMk j
  let rg : D.toGrp ⟶ Qg := Grp.homMk r
  have hqg : qg ≫ jg = ρ := (Grp.forget (Over S)).map_injective hq
  have hrg : rg ≫ jg = e := (Grp.forget (Over S)).map_injective hr
  exact ⟨⟨Qg, qg, jg, rg, p, hqg, hrg, hj, hmono, hqf, hqs, hql, hp, hps, hQsm, hQsep, hQqc⟩⟩

/-- The chosen smooth separated quasi-compact group quotient and its maps. -/
def groupFactorization : GroupFactorization ρ e :=
  Classical.choice (nonempty_groupFactorization ρ t π e hρ hcent he hπe hT)

end Group

namespace GroupFactorization

variable {ρ : G ⟶ L} {e : D.toGrp ⟶ L} (F : GroupFactorization ρ e)

/-- The torus in the quotient is closed if its given map to `L` is closed. -/
theorem isClosedSubgroup_torus (he : IsClosedSubgroup e) : IsClosedSubgroup F.torus := by
  let : Mono F.embedding.hom.hom.left := F.mono_embedding
  have he' : IsClosedImmersion e.hom.hom.left := he
  have : IsClosedImmersion (F.torus.hom.hom.left ≫ F.embedding.hom.hom.left) := by
    change IsClosedImmersion (F.torus ≫ F.embedding).hom.hom.left
    rwa [F.torus_fac]
  exact IsClosedImmersion.of_comp F.torus.hom.hom.left F.embedding.hom.hom.left

/-- Compatibility of the image torus in the quotient with the original homomorphisms. -/
theorem torus_comp (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) (h : π ≫ e = t ≫ ρ) :
    π ≫ F.torus = t ≫ F.projection := by
  let : Mono F.embedding.hom.hom.left := F.mono_embedding
  let : Mono F.embedding.hom.hom := Over.mono_of_mono_left _
  let : Mono F.embedding := (Grp.forget (Over S)).mono_of_mono_map
    (inferInstance : Mono F.embedding.hom.hom)
  apply (cancel_mono F.embedding).mp
  rw [Category.assoc, F.torus_fac, Category.assoc, F.projection_fac]
  exact h

end GroupFactorization

end Langlands.GroupScheme.TorusGraphQuotient
