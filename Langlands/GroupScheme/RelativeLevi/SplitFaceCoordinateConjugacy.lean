import Langlands.GroupScheme.Reductive.CoordinateTorusRootTransport
import Langlands.GroupScheme.RelativeLevi.SplitFaceRootRangeTransport
import Langlands.GroupScheme.RelativeLevi.SplitFaceParabolicAction

/-! # Equality of actual face terms under parabolic coordinate-torus conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G K : GroupScheme S} {F P : SubgroupFunctor G}
  (hn : F.IsNormalizedBy P) {g : Over.mk (𝟙 S) ⟶ G.X}
  (hg : g ∈ P.carrier (Over.mk (𝟙 S)))

include hn hg in
/-- Normalization identifies the actual subgroup with its preimage under
conjugation by any allowed base point. -/
theorem comap_innerIso_eq_of_isNormalizedBy : F.comap (G.innerIso g).hom = F := by
  apply ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_comap, G.comp_innerIso_hom]
  have hgT : G.constantPoint g T ∈ P.carrier T := P.comp_mem _ hg
  constructor
  · intro hx
    have h := hn T (G.constantPoint g T)⁻¹ _ (inv_mem hgT) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using h
  · exact hn T _ x hgT

include hn hg in
/-- The actual range of a representative is unchanged by this conjugation. -/
theorem range_comp_innerIso_eq_of_isNormalizedBy (v : K ⟶ G)
    (hv : range v = F) : range (v ≫ (G.innerIso g).hom) = range v := by
  apply ext
  intro T
  rw [range_comp_carrier]
  have heval : ((yonedaGrp.map (G.innerIso g).hom).app (Opposite.op T)).hom =
      (MulAut.conj (G.constantPoint g T)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact G.comp_innerIso_hom g T x
  rw [heval, congrArg (fun F => F.carrier T) hv]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hgT : G.constantPoint g T ∈ P.carrier T := P.comp_mem _ hg
  constructor
  · exact hn T _ x hgT
  · intro hx
    have h := hn T (G.constantPoint g T)⁻¹ _ (inv_mem hgT) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using h

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} [IsAffine S] {G P U : GroupScheme S} [IsAffineHom G.X.hom]
  (χ χ' : (Gm S).toGrp ⟶ G) {iP : P ⟶ G} (r : U ⟶ P)

/-- Two arbitrary cocharacters presenting one supplied relative parabolic and
radical have equal actual contracting functors, without a common-torus premise. -/
theorem unipotent_eq_of_same_suppliedRadical (hG : IsReductive G)
    (hPar : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hPar' : (Dynamic.parabolic χ').IsRepresentedBy iP)
    (hr : IsRelativeUnipotentRadical r) : Dynamic.unipotent χ = Dynamic.unipotent χ' :=
  (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG χ hPar r hr).2.symm.trans
    (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG χ' hPar' r hr).2

end Langlands.GroupScheme.RelativeLevi

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  [DecidableEq I] [DecidableEq I']
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ G)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt) (D : SplitParabolicFaceChart j Q fam' wt')
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' G j Q)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter j wt'))
  (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
  (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X)
  (hg : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).carrier _)
  (hsquare : i ≫ (G.innerIso g).hom = precompTorus E j)

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

include hG hmax hmax' hP hQ hfam hfam' hU hg hsquare in
/-- Actual parabolic conjugacy with the specified coordinate-torus matrix
makes all original ambient face terms equal on every scheme test. -/
theorem range_inclusion_eq_of_coordinateConjugacy (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) =
    SubgroupFunctor.range (D.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) := by
  let f := G.innerIso g
  let e := rootDatumEquivOfCoordinateTorusIso E f hsquare hG hG hmax hmax' hP hQ
  have hr (a : J) : SubgroupFunctor.range (fam a ≫ f.hom) =
      SubgroupFunctor.range (fam' (e.indexEquiv a)) :=
    range_root_comp_coordinateTorusIso E f hsquare hG hG hmax hmax' hP hQ hfam hfam' a
  have hnU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsNormalizedBy
      (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)) := by
    rw [← C.represented.2]
    exact C.range_inclusion_isNormalizedBy_originalParabolic hG hmax hP hfam 0
  have hUf : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
      (Dynamic.unipotent (AffineRegularBorel.cocharacter j wt')).comap f.hom := by
    rw [← hU]
    exact (SubgroupFunctor.comap_innerIso_eq_of_isNormalizedBy hnU hg).symm
  let ef := C.sameContractingRootTransportTermIso D e f hr hfam hfam' hUf hG hmax' hQ d
  have hef : ef.hom ≫ (D.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) =
      (C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom :=
    C.sameContractingRootTransportTermIso_hom_comp D e f hr hfam hfam' hUf hG hmax' hQ d
  have ht : SubgroupFunctor.range ((C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom) =
      SubgroupFunctor.range (D.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) := by
    rw [← hef, SubgroupFunctor.range_iso_comp]
  have hn := C.range_inclusion_isNormalizedBy_originalParabolic hG hmax hP hfam d
  have hp := SubgroupFunctor.range_comp_innerIso_eq_of_isNormalizedBy hn hg
    (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) rfl
  exact hp.symm.trans ht

/-- The actual ambient-compatible comparison under coordinate-torus conjugacy
inside the original parabolic. -/
def coordinateConjugateTermIso (d : ℕ) : C.weights.groupScheme d ≅ D.weights.groupScheme d := by
  let c := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let b := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono (C.weights.inclusion d ≫ c).hom.hom := by
    change Mono ((C.weights.inclusion d).hom.hom ≫ c.hom.hom)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hm' : Mono (D.weights.inclusion d ≫ b).hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ b.hom.hom)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  let F := SubgroupFunctor.range (C.weights.inclusion d ≫ c)
  have hc : F.IsRepresentedBy (C.weights.inclusion d ≫ c) := ⟨hm, rfl⟩
  have hb : F.IsRepresentedBy (D.weights.inclusion d ≫ b) :=
    ⟨hm', (C.range_inclusion_eq_of_coordinateConjugacy D hG hmax hmax' hP hQ hfam hfam'
      hU E g hg hsquare d).symm⟩
  exact hc.isoOfIsRepresentedBy hb

/-- The conjugator disappears from the resulting actual ambient inclusions. -/
theorem coordinateConjugateTermIso_hom_comp (d : ℕ) :
    (C.coordinateConjugateTermIso D hG hmax hmax' hP hQ hfam hfam' hU E g hg hsquare d).hom ≫
      (D.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) =
      C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) := by
  unfold coordinateConjugateTermIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.SplitParabolicFaceChart
