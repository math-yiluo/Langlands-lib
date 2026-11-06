import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.MinimalParabolicSplitComponent
import Langlands.GroupScheme.Rational.PositiveLeviCentralizer

/-! # Original radicals and Levis in a reductive dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
    {G P H U : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (p : P ⟶ G) (hP : (parabolic χ).IsRepresentedBy p)

include hG hP

/-- In a connected reductive ambient group, every smooth connected normal
unipotent closed subgroup of the actual dynamic parabolic contracts. -/
theorem normal_subgroup_range_comp_le_unipotent_of_reductive
    (v : H ⟶ P) (hvc : IsClosedSubgroup v)
    (hn : (SubgroupFunctor.range v).IsNormal)
    (hH : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H) :
    SubgroupFunctor.range (v ≫ p) ≤ unipotent χ := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hZ := dynamicCentralizerReductive k G hG χ
    (Affine.centralizerScheme χ) (Affine.centralizerHom χ)
    (Affine.isClosedSubgroup_centralizerHom χ)
    (Affine.isRepresentedBy_centralizerHom χ)
  exact normal_subgroup_range_comp_le_unipotent χ (Affine.centralizerHom χ) p hP
    (Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP) v hvc hn
    (Affine.isRepresentedBy_centralizerHom χ)
    (Affine.isClosedSubgroup_centralizerHom χ) hH hc hu hZ.hasTrivialUnipotentRadical

/-- Every supplied ground-field unipotent radical of the represented dynamic
parabolic has exactly the original identity-limit image on all test schemes. -/
theorem range_comp_radical_eq_unipotent_of_reductive
    (r : U ⟶ P) (hr : IsUnipotentRadical r) :
    SubgroupFunctor.range (r ≫ p) = unipotent χ := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  exact le_antisymm
    (normal_subgroup_range_comp_le_unipotent_of_reductive hG χ p hP r
      hr.isClosedSubgroup hr.isNormal hr.smooth hr.connectedSpace hr.isUnipotent)
    (unipotent_le_range_of_isUnipotentRadical χ p hP r hr)

end Dynamic

section Levi

variable {k : Type u} [Field k]
    {G P L : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : L ⟶ P}

/-- A cocharacter in the original rational Levi identifies that Levi with
its full ambient centralizer whenever the original parabolic is its dynamic
parabolic. No second Levi or centralizer representative is assumed. -/
theorem IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L)
    (hP : (Dynamic.parabolic (χ ≫ l ≫ p)).IsRepresentedBy p) :
    Dynamic.centralizer (χ ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth L.X.hom := hl.isConnectedReductive.smooth
  let : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic
    (χ ≫ l ≫ p) hP
  have hLp : SubgroupFunctor.range (l ≫ p) ≤
      Dynamic.parabolic (χ ≫ l ≫ p) := by
    rw [← hP.2]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨y ≫ l.hom.hom, Category.assoc _ _ _⟩
  have hfixed : SubgroupFunctor.range (l ≫ p) ≤
      Dynamic.centralizer (χ ≫ l ≫ p) := by
    exact Dynamic.range_le_centralizer_of_range_le_parabolic
      hl.isConnectedReductive.hasTrivialUnipotentRadical χ (l ≫ p)
      (hl.isClosedSubgroup.comp hpc) hLp
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  have hcontract := Dynamic.normal_subgroup_range_comp_le_unipotent_of_reductive
    hG (χ ≫ l ≫ p) p hP r hr.1.isClosedSubgroup hr.1.isNormal
    hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  exact Dynamic.centralizer_eq_of_subgroupMultiplication l r p (χ ≫ l ≫ p)
    hfixed hcontract ((Dynamic.centralizer_le_parabolic _).trans hP.2.ge)

set_option maxHeartbeats 800000 in
/-- A central commutative subgroup of the original Levi has that Levi as its
whole-group centralizer if one of its cocharacters presents the original
parabolic. Splitness and ambient maximality are separate assertions. -/
theorem IsRationalLeviSubgroup.torusCentralizer_eq_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ L) (ha : IsCentral a)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ A.toGrp)
    (hP : (Dynamic.parabolic (ν ≫ a ≫ l ≫ p)).IsRepresentedBy p) :
    torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) := by
  have hP' : (Dynamic.parabolic ((ν ≫ a) ≫ l ≫ p)).IsRepresentedBy p := by
    rw [Category.assoc]
    exact hP
  have hZ := hl.centralizer_eq_of_dynamicParabolic hG (ν ≫ a) hP'
  simp only [Category.assoc] at hZ
  exact le_antisymm
    ((torusCentralizer_le_dynamicCentralizer (a ≫ l ≫ p) ν).trans hZ.le)
    (IsCentral.range_le_torusCentralizer_comp a ha (l ≫ p))

section Iso

variable (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ L) (ha : IsCentral a)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ A.toGrp)
    (hP : (Dynamic.parabolic (ν ≫ a ≫ l ≫ p)).IsRepresentedBy p)
    {M : GroupScheme (Spec (CommRingCat.of k))} {m : M ⟶ G}
    (hm : (torusCentralizer (a ≫ l ≫ p)).IsRepresentedBy m)

include hl hG ha hP hm

/-- The original Levi is isomorphic to any supplied whole-group centralizer
representative when the given cocharacter presents the original parabolic. -/
def IsRationalLeviSubgroup.torusCentralizerIsoOfDynamicParabolic : L ≅ M := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic
    (ν ≫ a ≫ l ≫ p) hP
  let : IsClosedImmersion p.hom.hom.left := hpc
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono (l ≫ p).hom.hom := by
    change Mono (l.hom.hom ≫ p.hom.hom)
    infer_instance
  have heq := hl.torusCentralizer_eq_of_dynamicParabolic hG a ha ν hP
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (torusCentralizer (a ≫ l ≫ p)).IsRepresentedBy (l ≫ p) from
      ⟨inferInstance, heq.symm⟩) hm

@[simp]
theorem IsRationalLeviSubgroup.torusCentralizerIsoOfDynamicParabolic_hom_comp :
    (hl.torusCentralizerIsoOfDynamicParabolic hG a ha ν hP hm).hom ≫ m =
      l ≫ p := by
  unfold IsRationalLeviSubgroup.torusCentralizerIsoOfDynamicParabolic
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[simp]
theorem IsRationalLeviSubgroup.torusCentralizerIsoOfDynamicParabolic_inv_comp :
    (hl.torusCentralizerIsoOfDynamicParabolic hG a ha ν hP hm).inv ≫ l ≫ p =
      m := by
  have h := congrArg (fun f : L ⟶ G =>
    (hl.torusCentralizerIsoOfDynamicParabolic hG a ha ν hP hm).inv ≫ f)
    (hl.torusCentralizerIsoOfDynamicParabolic_hom_comp hG a ha ν hP hm)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

end Iso

end Levi

end Langlands.GroupScheme
