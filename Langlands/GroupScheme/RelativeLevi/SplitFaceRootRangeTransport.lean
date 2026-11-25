import Langlands.GroupScheme.RelativeLevi.SplitFaceAllRootPresentation
import Langlands.LinearAlgebra.RootDatumFaceTransport
import Langlands.GroupScheme.RelativeLevi.SplitFaceBaseComparison
import Langlands.GroupScheme.RelativeLevi.SplitRootSignDetection

/-! # Actual face-term transport from compatible full root ranges -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent Langlands.GroupTheory
open Langlands.LinearAlgebra.RootDatumFaceHeight
open Langlands.LinearAlgebra.RootDatumFaceTransport
open Langlands.LinearAlgebra.RootDatumFaceBaseComparison

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ H)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (D : SplitParabolicFaceChart j Q fam' wt')
  (e : RootPairing.Equiv P Q)

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
private local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Match the entire two root families through a full root-datum equivalence. -/
def rootTransportIndex : Fin (Nat.card J) ≃ Fin (Nat.card J') :=
  (allRootIndex J).trans (e.indexEquiv.trans (allRootIndex J').symm)

@[simp] theorem rootTransportIndex_label (k : Fin (Nat.card J)) :
    (allRootIndex J') (rootTransportIndex e k) = e.indexEquiv ((allRootIndex J) k) := by
  simp [rootTransportIndex]

variable (f : G ≅ H)
  (hroot : ∀ a : J, SubgroupFunctor.range (fam a ≫ f.hom) =
    SubgroupFunctor.range (fam' (e.indexEquiv a)))
  (hheight : ∀ a : J,
    faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
      faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))

include hroot hheight in
/-- Equal full-root heights and actual transported root ranges identify every
ambient term on every scheme test, even for different coordinate tori. -/
theorem range_inclusion_comp_eq_of_rootTransport (d : ℕ) :
    SubgroupFunctor.range ((C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom) =
    SubgroupFunctor.range (D.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) := by
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.range_comp_carrier, C.range_inclusion_comp_eq_allRootSubgroup,
    D.range_inclusion_comp_eq_allRootSubgroup]
  change (HeightFiltration.level (rootFactor fam (allRootIndex J) T)
    (fun k => C.allRootWeight ((allRootIndex J) k)) (d + 1)).map
      ((yonedaGrp.map f.hom).app (Opposite.op T)).hom =
    HeightFiltration.level (rootFactor fam' (allRootIndex J') T)
      (fun k => D.allRootWeight ((allRootIndex J') k)) (d + 1)
  rw [HeightFiltration.map_level]
  apply HeightFiltration.level_eq_of_equiv _ _ _ _ (rootTransportIndex e) _ _ (d + 1)
  · intro k
    rw [map_rootFactor, rootFactor_eq_range, rootFactor_eq_range, rootTransportIndex_label]
    exact congrArg (fun F => F.carrier T) (hroot ((allRootIndex J) k))
  · intro k
    rw [rootTransportIndex_label]
    exact congrArg Int.toNat (hheight ((allRootIndex J) k))

/-- The actual inclusion-compatible term isomorphism obtained from transported
root ranges and exact unscaled face heights. -/
def rootTransportTermIso (d : ℕ) : C.weights.groupScheme d ≅ D.weights.groupScheme d := by
  let c := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let b := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono ((C.weights.inclusion d ≫ c) ≫ f.hom).hom.hom := by
    change Mono (((C.weights.inclusion d).hom.hom ≫ c.hom.hom) ≫ f.hom.hom.hom)
    exact mono_comp' (mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1) inferInstance
  have hm' : Mono (D.weights.inclusion d ≫ b).hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ b.hom.hom)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  let F := SubgroupFunctor.range ((C.weights.inclusion d ≫ c) ≫ f.hom)
  have hc : F.IsRepresentedBy ((C.weights.inclusion d ≫ c) ≫ f.hom) := ⟨hm, rfl⟩
  have hb : F.IsRepresentedBy (D.weights.inclusion d ≫ b) :=
    ⟨hm', (C.range_inclusion_comp_eq_of_rootTransport D e f hroot hheight d).symm⟩
  exact hc.isoOfIsRepresentedBy hb

/-- The comparison retains exactly the transported original ambient map. -/
theorem rootTransportTermIso_hom_comp (d : ℕ) :
    (C.rootTransportTermIso D e f hroot hheight d).hom ≫
      (D.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) =
      (C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom := by
  unfold rootTransportTermIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

section HeightFromSigns

variable [Nontrivial R]
  (hH : IsReductive H)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)
  (hpos : ∀ a : J, 0 < coPairing (P.root a) wt ↔
    0 < coPairing (Q.root (e.indexEquiv a)) wt')
  (hzero : ∀ a : J, coPairing (P.root a) wt = 0 ↔
    coPairing (Q.root (e.indexEquiv a)) wt' = 0)

include hH hmax hQ hpos hzero in
/-- The compatible positive/zero-root face determines exact transported
unscaled face heights; the positive bases may be unrelated. -/
theorem faceHeight_root_eq_of_rootSigns (a : J) :
    faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
      faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)) := by
  classical
  let : Q.IsReduced := hQ.isReduced
  let := hQ.finite_zeroReflectionSubgroup hH hmax D.faceCoweight
  have hdom : ∀ b ∈ (C.base.map e).support, 0 ≤ Q.root' b D.faceCoweight := by
    intro b hb
    rw [RootPairing.Base.support_map_eq] at hb
    obtain ⟨b, hb', he⟩ := Finset.mem_image.mp hb
    rw [← he, D.coweight_eq]
    have hp := C.dominant b hb'
    rw [C.coweight_eq] at hp
    by_cases hz : coPairing (P.root b) wt = 0
    · rw [(hzero b).mp hz]
    · exact le_of_lt ((hpos b).mp (by omega))
  have hf : faceHeight (C.base.map e) (e.coweightEquiv.symm C.faceCoweight) =
      faceHeight D.base D.faceCoweight := by
    calc
      _ = faceHeight (C.base.map e) D.faceCoweight := by
        apply faceHeight_eq_of_simple_zero_iff
        intro b hb
        rw [RootPairing.Base.support_map_eq] at hb
        obtain ⟨b, hb', he⟩ := Finset.mem_image.mp hb
        rw [← he, e.root'_coweightEquiv, C.coweight_eq, D.coweight_eq]
        exact hzero b
      _ = faceHeight D.base D.faceCoweight :=
        faceHeight_eq_of_dominant_bases Q (C.base.map e) D.base D.faceCoweight hdom D.dominant
  have ht := LinearMap.congr_fun (faceHeight_map e C.base C.faceCoweight) (P.rootSpanMem ℤ a)
  rw [LinearMap.comp_apply, rootSpanMap_root, hf] at ht
  exact ht.symm

end HeightFromSigns

section ActualContracting

variable [Nontrivial R]
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
    (Dynamic.unipotent (AffineRegularBorel.cocharacter j wt')).comap f.hom)

include hroot hfam hfam' hU in
/-- Actual transported root ranges and actual contracting-group compatibility
force equality of the strictly positive root signs. -/
theorem coPairing_pos_iff_of_rootTransport (a : J) :
    0 < coPairing (P.root a) wt ↔ 0 < coPairing (Q.root (e.indexEquiv a)) wt' := by
  have hu : TorusEquivariant i (fun a => P.root a) fam :=
    fun a T t c => (hfam a).equivariant T t c
  have hu' : TorusEquivariant j (fun a => Q.root a) fam' :=
    fun a T t c => (hfam' a).equivariant T t c
  rw [coPairing_pos_iff_range_root_le_unipotent hu wt a (hfam a),
    coPairing_pos_iff_range_root_le_unipotent hu' wt' (e.indexEquiv a) (hfam' _),
    ← hroot a]
  constructor
  · intro h T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy := h T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    rw [hU] at hy
    change (y ≫ (fam a).hom.hom) ≫ f.hom.hom.hom ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter j wt')).carrier T
    exact hy
  · intro h T x hx
    rw [hU]
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ (fam a).hom.hom) ≫ f.hom.hom.hom ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter j wt')).carrier T
    apply h T
    exact SubgroupFunctor.mem_range.mpr ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

include hroot hfam hfam' hU in
/-- Actual root and contracting transport also determines precisely the
zero-root face, by applying sign detection to each root and its negative. -/
theorem coPairing_zero_iff_of_rootTransport (a : J) :
    coPairing (P.root a) wt = 0 ↔ coPairing (Q.root (e.indexEquiv a)) wt' = 0 := by
  let := P.indexNeg
  have hp := coPairing_pos_iff_of_rootTransport e f hroot hfam hfam' hU a
  have hn := coPairing_pos_iff_of_rootTransport e f hroot hfam hfam' hU (-a)
  have hrp : P.root (-a) = -P.root a := by
    change P.root (P.reflectionPerm a a) = _
    simp
  have hrq : Q.root (e.indexEquiv (-a)) = -Q.root (e.indexEquiv a) := by
    rw [← e.root_weightMap_apply P Q (-a), ← e.root_weightMap_apply P Q a,
      hrp, map_neg]
  change 0 < coPairingLinear wt (P.root (-a)) ↔
    0 < coPairingLinear wt' (Q.root (e.indexEquiv (-a))) at hn
  rw [hrp, hrq, map_neg, map_neg] at hn
  change (0 < -coPairing (P.root a) wt ↔
    0 < -coPairing (Q.root (e.indexEquiv a)) wt') at hn
  omega

variable (hH : IsReductive H)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)

/-- Actual compatible root ranges and contracting groups give inclusion-compatible
isomorphisms of every original unscaled face term across different tori. -/
def sameContractingRootTransportTermIso (d : ℕ) :
    C.weights.groupScheme d ≅ D.weights.groupScheme d :=
  C.rootTransportTermIso D e f hroot
    (C.faceHeight_root_eq_of_rootSigns D e hH hmax hQ
      (coPairing_pos_iff_of_rootTransport e f hroot hfam hfam' hU)
      (coPairing_zero_iff_of_rootTransport e f hroot hfam hfam' hU)) d

/-- The comparison preserves the original maps after the actual ambient isomorphism. -/
theorem sameContractingRootTransportTermIso_hom_comp (d : ℕ) :
    (C.sameContractingRootTransportTermIso D e f hroot hfam hfam' hU hH hmax hQ d).hom ≫
      (D.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)) =
      (C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom := by
  unfold sameContractingRootTransportTermIso
  exact rootTransportTermIso_hom_comp _ _ _ _ _ _ _

end ActualContracting

end Langlands.GroupScheme.SplitParabolicFaceChart
