import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.Torsion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u
variable {S S' : Scheme.{u}}

private def kernelCongr {G H : Grp (Over S)} {f g : G ⟶ H} (h : f = g) :
    kernel f ≅ kernel g :=
  eqToIso (congrArg kernel h)

private lemma kernelCongr_hom_ι {G H : Grp (Over S)} {f g : G ⟶ H} (h : f = g) :
    (kernelCongr h).hom ≫ kernelι g = kernelι f := by
  subst g
  simp [kernelCongr]

/-- Integer torsion commutes with arbitrary change of base. -/
def torsionBaseChangeIso (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) :
    (Over.pullback b).mapGrp.obj (torsion G n) ≅
      torsion ((Over.pullback b).mapGrp.obj G) n :=
  kernelBaseChangeIso b (multiplication G n) ≪≫
    kernelCongr (multiplication_baseChange b G n)

@[reassoc (attr := simp)]
lemma torsionBaseChangeIso_hom_ι (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) :
    (torsionBaseChangeIso b G n).hom ≫ torsionι ((Over.pullback b).mapGrp.obj G) n =
      (Over.pullback b).mapGrp.map (torsionι G n) := by
  simp only [torsionBaseChangeIso, Iso.trans_hom, torsionι, Category.assoc,
    kernelCongr_hom_ι, kernelBaseChangeIso_hom_ι]

@[reassoc (attr := simp)]
lemma torsionBaseChangeIso_inv_ι (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) :
    (torsionBaseChangeIso b G n).inv ≫ (Over.pullback b).mapGrp.map (torsionι G n) =
      torsionι ((Over.pullback b).mapGrp.obj G) n := by
  rw [← torsionBaseChangeIso_hom_ι b G n, Iso.inv_hom_id_assoc]

/-- The inclusion equation uniquely determines the comparison morphism. -/
lemma torsionBaseChangeIso_hom_unique (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ)
    (g : (Over.pullback b).mapGrp.obj (torsion G n) ⟶
      torsion ((Over.pullback b).mapGrp.obj G) n)
    (hg : g ≫ torsionι ((Over.pullback b).mapGrp.obj G) n =
      (Over.pullback b).mapGrp.map (torsionι G n)) :
    g = (torsionBaseChangeIso b G n).hom := by
  apply Grp.hom_ext
  apply (cancel_mono (torsionι ((Over.pullback b).mapGrp.obj G) n).hom.hom).mp
  change (g ≫ torsionι ((Over.pullback b).mapGrp.obj G) n).hom.hom =
    ((torsionBaseChangeIso b G n).hom ≫
      torsionι ((Over.pullback b).mapGrp.obj G) n).hom.hom
  rw [hg, torsionBaseChangeIso_hom_ι]

/-- Pullback adjunction identifies the actual torsion subgroups on every test scheme. -/
def baseChangeTorsionPointsEquiv (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) (T : Over S') :
    torsionPoints ((Over.pullback b).mapGrp.obj G) n T ≃*
      torsionPoints G n ((Over.map b).obj T) where
  toFun x := ⟨baseChangePointsEquiv b G T x.val, by
    apply (mem_torsionPoints G n _ _).mpr
    rw [← map_zpow, (mem_torsionPoints _ n T _).mp x.property, map_one]⟩
  invFun x := ⟨(baseChangePointsEquiv b G T).symm x.val, by
    apply (mem_torsionPoints _ n T _).mpr
    rw [← map_zpow, (mem_torsionPoints G n _ _).mp x.property, map_one]⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((baseChangePointsEquiv b G T).map_mul x.val y.val)

@[simp]
lemma baseChangeTorsionPointsEquiv_val (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) (T : Over S')
    (x : torsionPoints ((Over.pullback b).mapGrp.obj G) n T) :
    (baseChangeTorsionPointsEquiv b G n T x).val =
      baseChangePointsEquiv b G T x.val := rfl

lemma baseChangeTorsionPointsEquiv_naturality (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) {T T' : Over S'} (a : T' ⟶ T)
    (x : torsionPoints ((Over.pullback b).mapGrp.obj G) n T) :
    baseChangeTorsionPointsEquiv b G n T'
      (torsionPointsRestrict ((Over.pullback b).mapGrp.obj G) n a x) =
      torsionPointsRestrict G n ((Over.map b).map a)
        (baseChangeTorsionPointsEquiv b G n T x) :=
  Subtype.ext (baseChangePointsEquiv_naturality b G a x.val)

/-- The scheme comparison agrees with the canonical torsion-point identifications. -/
lemma torsionBaseChangeIso_points (b : S' ⟶ S) (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℤ) (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (torsion G n)).X) :
    baseChangeTorsionPointsEquiv b G n T
      (torsionPointsEquiv ((Over.pullback b).mapGrp.obj G) n T
        (x ≫ (torsionBaseChangeIso b G n).hom.hom.hom)) =
      torsionPointsEquiv G n ((Over.map b).obj T)
        (baseChangePointsEquiv b (torsion G n) T x) := by
  apply Subtype.ext
  change baseChangePointsEquiv b G T
    ((x ≫ (torsionBaseChangeIso b G n).hom.hom.hom) ≫
      (torsionι ((Over.pullback b).mapGrp.obj G) n).hom.hom) =
    baseChangePointsEquiv b (torsion G n) T x ≫ (torsionι G n).hom.hom
  rw [← baseChangePointsEquiv_comp b (torsionι G n) T]
  congr 1
  rw [Category.assoc]
  congr 1
  exact congrArg (fun k => k.hom.hom) (torsionBaseChangeIso_hom_ι b G n)

end Langlands.GroupScheme
