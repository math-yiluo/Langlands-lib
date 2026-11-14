import Langlands.GroupScheme.Reductive.IsogenyKernelOpenCell
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.SplitTorusKernelCentralityProof

/-! # Full-kernel centrality from injectivity on opposite unipotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S}
  [IsSeparated G.X.hom] [IsSeparated H.X.hom]

/-- If a homomorphism kills no nontrivial point of the dynamic unipotent,
then every point it kills in the dynamic parabolic lies in the dynamic centralizer. -/
theorem mem_centralizer_of_comp_eq_one_of_unipotent_kernel
    (χ : (Gm S).toGrp ⟶ G) (q : G ⟶ H)
    (hkill : ∀ (V : Over S) (x : V ⟶ G.X),
      x ∈ (unipotent χ).carrier V → x ≫ q.hom.hom = 1 → x = 1)
    {V : Over S} (g : V ⟶ G.X)
    (hgP : g ∈ (parabolic χ).carrier V) (hg : g ≫ q.hom.hom = 1) :
    g ∈ (centralizer χ).carrier V := by
  let p : (parabolic χ).carrier V := ⟨g, hgP⟩
  have hlq := (hasLimit_limit χ p).comp_hom χ q
  rw [hg] at hlq
  have hl1 := hasLimit_of_mem_centralizer (χ ≫ q)
    (show (1 : V ⟶ H.X) ∈ (centralizer (χ ≫ q)).carrier V from one_mem _)
  have he : limit χ p ≫ q.hom.hom = 1 := hlq.unique (χ ≫ q) hl1
  have hu := mul_inv_limit_mem_unipotent χ p
  have huq : (g * (limit χ p)⁻¹) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hg, he, inv_one, mul_one]
  have h1 := hkill V _ hu huq
  have hge : g = limit χ p := mul_inv_eq_one.mp h1
  rw [hge]
  exact limit_mem_centralizer χ p

end Dynamic

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A finite homomorphism injective on both opposite dynamic unipotents has
its full kernel in a self-centralizing torus equal to the dynamic centralizer. -/
theorem range_kernelι_le_torus_of_unipotent_kernels
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hcent : Dynamic.centralizer χ = SubgroupFunctor.range i)
    (hplus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent χ).carrier V → x ≫ q.hom.hom = 1 → x = 1)
    (hminus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier V →
        x ≫ q.hom.hom = 1 → x = 1) :
    SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let U := Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)
  let P := Dynamic.Affine.parabolicScheme χ
  let iU : U ⟶ G := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  let iP : P ⟶ G := Dynamic.Affine.parabolicHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom
    (Dynamic.oppositeCocharacter χ)
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let c := SubgroupFunctor.cellMultiplication iU iP
  have : IsOpenImmersion c.left := oppositeCellStatement k G χ _ _ _ _ hU hP
  have hle : SubgroupFunctor.range i ≤ Dynamic.parabolic χ := by
    rw [← hcent]
    exact Dynamic.centralizer_le_parabolic χ
  let aP := hP.factorHom i hle
  let a := lift (1 : T.X ⟶ U.X) aP.hom.hom
  have ha : a ≫ c = i.hom.hom := by
    simp only [a, c, SubgroupFunctor.lift_cellMultiplication,
      MonObj.one_comp, one_mul]
    exact congrArg (fun z => z.hom.hom) (hP.factorHom_comp i hle)
  let κ := kernelOpenCellLift q hT i hself c a ha
  have hκ : κ ≫ c = (kernelι q).hom.hom := kernelOpenCellLift_fac _ _ _ _ _ _ _
  intro V g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  let z := x ≫ κ
  let un := z ≫ fst U.X P.X ≫ iU.hom.hom
  let pp := z ≫ snd U.X P.X ≫ iP.hom.hom
  have hun : un ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier V := by
    rw [← hU.2]
    exact SubgroupFunctor.mem_range.mpr ⟨z ≫ fst _ _, rfl⟩
  have hpp : pp ∈ (Dynamic.parabolic χ).carrier V := by
    rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨z ≫ snd _ _, rfl⟩
  have hprod : un * pp = x ≫ (kernelι q).hom.hom := by
    have he := congrArg (x ≫ ·) hκ
    simpa only [κ, c, z, un, pp, SubgroupFunctor.cellMultiplication,
      MonObj.comp_mul, Category.assoc] using he
  have hk : (un * pp) ≫ q.hom.hom = 1 := by
    rw [hprod]
    exact (kernelPointsEquiv q V x).property
  have hunq : un ≫ q.hom.hom ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (χ ≫ q))).carrier V := by
    have he := Dynamic.unipotent_le_comap (Dynamic.oppositeCocharacter χ) q V hun
    simpa only [SubgroupFunctor.mem_comap, Dynamic.oppositeCocharacter,
      Category.assoc] using he
  have hppq : pp ≫ q.hom.hom ∈ (Dynamic.parabolic (χ ≫ q)).carrier V :=
    Dynamic.parabolic_le_comap χ q V hpp
  have hunP : un ≫ q.hom.hom ∈ (Dynamic.parabolic (χ ≫ q)).carrier V := by
    rw [MonObj.mul_comp] at hk
    rw [mul_eq_one_iff_eq_inv.mp hk]
    exact Subgroup.inv_mem _ hppq
  have hunq1 : un ≫ q.hom.hom = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic (χ ≫ q) hunq hunP
  have hun1 : un = 1 := hminus V un hun hunq1
  have hgp : x ≫ (kernelι q).hom.hom ∈ (Dynamic.parabolic χ).carrier V := by
    rw [hun1, one_mul] at hprod
    rwa [← hprod]
  rw [← hcent]
  exact Dynamic.mem_centralizer_of_comp_eq_one_of_unipotent_kernel χ q hplus
    _ hgp (kernelPointsEquiv q V x).property

section Factor

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hcent : Dynamic.centralizer χ = SubgroupFunctor.range i)
    (hplus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent χ).carrier V → x ≫ q.hom.hom = 1 → x = 1)
    (hminus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier V →
        x ≫ q.hom.hom = 1 → x = 1)

/-- Factor the full finite kernel through a closed torus using the two
opposite unipotent kernel conditions. -/
def kernelTorusFactorOfUnipotentKernels : kernel q ⟶ T.toGrp := by
  have : IsClosedImmersion i.hom.hom.left := hi
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact hr.factorHom (kernelι q)
    (range_kernelι_le_torus_of_unipotent_kernels q hT i hself χ hcent hplus hminus)

theorem kernelTorusFactorOfUnipotentKernels_comp :
    kernelTorusFactorOfUnipotentKernels q hT i hi hself χ hcent hplus hminus ≫ i =
      kernelι q := by
  unfold kernelTorusFactorOfUnipotentKernels
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end Factor

end Langlands.GroupScheme
