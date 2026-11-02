import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.AbelianScheme.Kernel

/-! # The limit homomorphism, its kernel and the Levi decomposition as morphisms of schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

open SubgroupFunctor.IsRepresentedBy

variable {S : Scheme.{u}} {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {P Z U : GroupScheme S} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}

section Limit

variable (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)

/-- The limit at zero as a homomorphism of group schemes `P_G(χ) ⟶ Z_G(χ)`, for representing
group schemes `P` and `Z`. -/
def limitGroupHom : P ⟶ Z :=
  hP.lift hZ (limitHom χ) (fun a g => limitHom_comp χ a g)

/-- On points, `limitGroupHom` is the limit at zero. -/
theorem limitGroupHom_comp {T : Over S} (x : T ⟶ P.X) :
    (x ≫ (limitGroupHom hP hZ).hom.hom) ≫ iZ.hom.hom = limit χ (hP.pointsEquiv T x) :=
  lift_comp hP hZ _ _ x

/-- The inclusion `Z_G(χ) ⟶ P_G(χ)` of representing group schemes. -/
def centralizerToParabolic : Z ⟶ P :=
  hZ.lift hP (fun T => Subgroup.inclusion (centralizer_le_parabolic χ T)) (fun _ _ => rfl)

omit [IsSeparated G.X.hom] in
theorem centralizerToParabolic_comp : centralizerToParabolic hP hZ ≫ iP = iZ :=
  lift_comp_eq hZ hP _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- The inclusion `Z_G(χ) ⟶ P_G(χ)` is a section of the limit homomorphism. -/
theorem centralizerToParabolic_comp_limitGroupHom :
    centralizerToParabolic hP hZ ≫ limitGroupHom hP hZ = 𝟙 Z := by
  apply hom_ext hZ
  rw [Category.id_comp]
  apply (Grp.forget (Over S)).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  change (centralizerToParabolic hP hZ).hom.hom ≫ (limitGroupHom hP hZ).hom.hom ≫ iZ.hom.hom =
    iZ.hom.hom
  rw [← Category.assoc, limitGroupHom_comp]
  have hc : (hP.pointsEquiv Z.X (centralizerToParabolic hP hZ).hom.hom : Z.X ⟶ G.X) =
      iZ.hom.hom :=
    congrArg (fun f : Z ⟶ G => f.hom.hom) (centralizerToParabolic_comp hP hZ)
  have hmem : (hP.pointsEquiv Z.X (centralizerToParabolic hP hZ).hom.hom : Z.X ⟶ G.X) ∈
      (centralizer χ).carrier Z.X := by
    rw [hc, ← Category.id_comp iZ.hom.hom]
    exact (hZ.pointsEquiv Z.X (𝟙 _)).2
  rw [limit_eq χ (hasLimit_of_mem_centralizer χ hmem), hc]

end Limit

section Kernel

omit [IsSeparated G.X.hom] in
theorem grp_comp_hom_hom {A B C : GroupScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom :=
  rfl

omit [IsSeparated G.X.hom] in
/-- A point of a kernel, followed by the kernel inclusion, is killed by the homomorphism. -/
theorem kernelι_comp_eq_one {A B : GroupScheme S} (f : A ⟶ B) {T : Over S}
    (y : T ⟶ (kernel f).X) : (y ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1 :=
  (kernelPointsEquiv f T y).2

omit [IsSeparated G.X.hom] in
/-- A point killed by the homomorphism factors through the kernel. -/
theorem exists_kernel_point {A B : GroupScheme S} (f : A ⟶ B) {T : Over S} (p : T ⟶ A.X)
    (hp : p ≫ f.hom.hom = 1) : ∃ y : T ⟶ (kernel f).X, y ≫ (kernelι f).hom.hom = p :=
  ⟨(kernelPointsEquiv f T).symm ⟨p, hp⟩,
    congrArg Subtype.val ((kernelPointsEquiv f T).apply_symm_apply ⟨p, hp⟩)⟩

variable (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)

/-- `U_G(χ)` is represented by the kernel of the limit homomorphism `P_G(χ) ⟶ Z_G(χ)`. -/
theorem isRepresentedBy_kernel_limitGroupHom :
    (unipotent χ).IsRepresentedBy (kernelι (limitGroupHom hP hZ) ≫ iP) := by
  have hPm : Mono iP.hom.hom := hP.1
  have hZm : Mono iZ.hom.hom := hZ.1
  refine ⟨?_, ?_⟩
  · rw [grp_comp_hom_hom]
    exact mono_comp _ _
  ext T x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [grp_comp_hom_hom, ← Category.assoc]
    have h1 := limitGroupHom_comp hP hZ (y ≫ (kernelι (limitGroupHom hP hZ)).hom.hom)
    rw [kernelι_comp_eq_one, MonObj.one_comp] at h1
    have h2 := (limit_eq_one_iff χ _).1 h1.symm
    rwa [pointsEquiv_apply_coe] at h2
  · intro hx
    have hxP : x ∈ (parabolic χ).carrier T := unipotent_le_parabolic χ T hx
    have hpx : (hP.pointsEquiv T).symm ⟨x, hxP⟩ ≫ iP.hom.hom = x := pointsEquiv_symm_comp hP _
    have hl : (hP.pointsEquiv T).symm ⟨x, hxP⟩ ≫ (limitGroupHom hP hZ).hom.hom = 1 := by
      apply hZm.right_cancellation
      rw [limitGroupHom_comp, MonObj.one_comp, MulEquiv.apply_symm_apply]
      exact (limit_eq_one_iff χ ⟨x, hxP⟩).2 hx
    obtain ⟨y, hy⟩ := exists_kernel_point _ _ hl
    refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
    rw [grp_comp_hom_hom, ← Category.assoc, hy, hpx]

variable {hP hZ}

/-- A representing group scheme of `U_G(χ)` is the kernel of the limit homomorphism, compatibly
with the inclusions into `G`. -/
def unipotentIsoKernel (hU : (unipotent χ).IsRepresentedBy iU) :
    U ≅ kernel (limitGroupHom hP hZ) :=
  isoOfIsRepresentedBy hU (isRepresentedBy_kernel_limitGroupHom hP hZ)

theorem unipotentIsoKernel_hom_comp (hU : (unipotent χ).IsRepresentedBy iU) :
    (unipotentIsoKernel (hP := hP) (hZ := hZ) hU).hom ≫ kernelι (limitGroupHom hP hZ) ≫ iP =
      iU :=
  isoOfIsRepresentedBy_hom_comp hU (isRepresentedBy_kernel_limitGroupHom hP hZ)

end Kernel

section Multiplication

variable (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)

/-- The multiplication morphism `U_G(χ) ×_S Z_G(χ) ⟶ P_G(χ)`, `(u, z) ↦ u z`. -/
def multiplication : U.X ⊗ Z.X ⟶ P.X :=
  (hP.pointsEquiv _).symm
    ⟨(fst U.X Z.X ≫ iU.hom.hom) * (snd U.X Z.X ≫ iZ.hom.hom),
      mul_mem (unipotent_le_parabolic χ _ (hU.pointsEquiv _ (fst U.X Z.X)).2)
        (centralizer_le_parabolic χ _ (hZ.pointsEquiv _ (snd U.X Z.X)).2)⟩

omit [IsSeparated G.X.hom] in
theorem multiplication_comp : multiplication hP hZ hU ≫ iP.hom.hom =
    (fst U.X Z.X ≫ iU.hom.hom) * (snd U.X Z.X ≫ iZ.hom.hom) :=
  pointsEquiv_symm_comp hP _

/-- On points, the multiplication morphism is the published semidirect product isomorphism
`U_G(χ)(T) ⋊ Z_G(χ)(T) ≃* P_G(χ)(T)`. -/
theorem pointsEquiv_comp_multiplication {T : Over S} (w : T ⟶ U.X ⊗ Z.X) :
    hP.pointsEquiv T (w ≫ multiplication hP hZ hU) =
      semidirectEquiv χ T ⟨hU.pointsEquiv T (w ≫ fst U.X Z.X), hZ.pointsEquiv T (w ≫ snd U.X Z.X)⟩ := by
  apply Subtype.ext
  change (w ≫ multiplication hP hZ hU) ≫ iP.hom.hom =
    ((w ≫ fst U.X Z.X) ≫ iU.hom.hom) * ((w ≫ snd U.X Z.X) ≫ iZ.hom.hom)
  rw [Category.assoc, multiplication_comp, MonObj.comp_mul, Category.assoc, Category.assoc]

/-- Conrad, Theorem 4.1.7(3): the multiplication morphism `U_G(χ) ×_S Z_G(χ) ⟶ P_G(χ)` is an
isomorphism of schemes over `S`. -/
theorem isIso_multiplication : IsIso (multiplication hP hZ hU) := by
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨fun w w' h => ?_, fun p => ?_⟩
  · have h' := congrArg (hP.pointsEquiv T) h
    simp only at h'
    rw [pointsEquiv_comp_multiplication, pointsEquiv_comp_multiplication] at h'
    have h'' := (semidirectEquiv χ T).injective h'
    have hl := (hU.pointsEquiv T).injective (congrArg SemidirectProduct.left h'')
    have hr := (hZ.pointsEquiv T).injective (congrArg SemidirectProduct.right h'')
    exact CartesianMonoidalCategory.hom_ext _ _ hl hr
  · set s := (semidirectEquiv χ T).symm (hP.pointsEquiv T p) with hs
    refine ⟨lift ((hU.pointsEquiv T).symm s.left) ((hZ.pointsEquiv T).symm s.right), ?_⟩
    apply (hP.pointsEquiv T).injective
    simp only
    rw [pointsEquiv_comp_multiplication, lift_fst, lift_snd, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact (semidirectEquiv χ T).apply_symm_apply _

/-- The isomorphism `U_G(χ) ×_S Z_G(χ) ≅ P_G(χ)` of schemes over `S` given by multiplication. -/
def multiplicationIso : U.X ⊗ Z.X ≅ P.X :=
  haveI := isIso_multiplication hP hZ hU
  asIso (multiplication hP hZ hU)

end Multiplication

end Langlands.GroupScheme.Dynamic
