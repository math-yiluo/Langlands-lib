import Langlands.AbelianScheme.Tate.FiniteMonodromy

/-! # Transport on actual finite torsion fibres along a geometric path -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj PreGaloisCategory
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u
namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

/-- Evaluate an isomorphism of the actual finite fibre functors on a cover. -/
def pathAct (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (Y : Over S) [IsFinite Y.hom] [Etale Y.hom] (x : Over.mk s ⟶ Y) :
    Over.mk t ⟶ Y :=
  p.hom.app (ofOver Y) x

theorem pathAct_naturality (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    {Y Z : Over S} [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom]
    (f : Y ⟶ Z) (x : Over.mk s ⟶ Y) :
    pathAct p Z (x ≫ f) = pathAct p Y x ≫ f :=
  ConcreteCategory.congr_hom (p.hom.naturality
    (ObjectProperty.homMk f : ofOver Y ⟶ ofOver Z)) x

theorem pathAct_lift (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (Y Z : Over S) [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom]
    (x : Over.mk s ⟶ Y) (y : Over.mk s ⟶ Z) :
    pathAct p (Y ⊗ Z) (lift x y) = lift (pathAct p Y x) (pathAct p Z y) := by
  apply hom_ext
  · rw [← pathAct_naturality, lift_fst, lift_fst]
  · rw [← pathAct_naturality, lift_snd, lift_snd]

theorem pathAct_one (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (G : Grp (Over S)) [IsFinite G.X.hom] [Etale G.X.hom] :
    pathAct p G.X (1 : Over.mk s ⟶ G.X) = 1 := by
  change pathAct p G.X (toUnit _ ≫ η[G.X]) = toUnit _ ≫ η[G.X]
  rw [pathAct_naturality]
  congr 1
  exact toUnit_unique _ _

theorem pathAct_mul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (G : Grp (Over S)) [IsFinite G.X.hom] [Etale G.X.hom]
    (x y : Over.mk s ⟶ G.X) :
    pathAct p G.X (x * y) = pathAct p G.X x * pathAct p G.X y := by
  change pathAct p G.X (lift x y ≫ μ[G.X]) = _
  rw [pathAct_naturality, pathAct_lift]
  rfl

/-- The induced isomorphism of the actual automorphism groups. -/
def pathConjugation (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    FundamentalGroup s hs ≃* FundamentalGroup t ht :=
  Aut.autMulEquivOfIso p

theorem continuous_pathConjugation (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (pathConjugation p) := by
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding (fiberFunctor t ht)).isInducing,
    continuous_pi_iff]
  intro Y
  change Continuous (fun g => Aut.autMulEquivOfIso (p.app Y)
    (PreGaloisCategory.autEmbedding (fiberFunctor s hs) g Y))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply Y).comp continuous_induced_dom)

/-- Path conjugation respects the existing profinite evaluation topologies. -/
def pathFundamentalGroupEquiv (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    FundamentalGroup s hs ≃ₜ* FundamentalGroup t ht where
  __ := pathConjugation p
  continuous_toFun := continuous_pathConjugation p
  continuous_invFun := continuous_pathConjugation p.symm

/-- Evaluation preserves the group law on points, with inverse given by the reverse path. -/
def groupPathTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (G : Grp (Over S)) [IsFinite G.X.hom] [Etale G.X.hom] :
    Additive (Over.mk s ⟶ G.X) ≃+ Additive (Over.mk t ⟶ G.X) where
  toFun x := Additive.ofMul (pathAct p G.X x.toMul)
  invFun x := Additive.ofMul (pathAct p.symm G.X x.toMul)
  left_inv x := ConcreteCategory.congr_hom (p.hom_inv_id_app (ofOver G.X)) x
  right_inv x := ConcreteCategory.congr_hom (p.inv_hom_id_app (ofOver G.X)) x
  map_add' x y := pathAct_mul p G x.toMul y.toMul

@[simp] theorem groupPathTransport_refl (G : Grp (Over S))
    [IsFinite G.X.hom] [Etale G.X.hom] (x : Additive (Over.mk s ⟶ G.X)) :
    groupPathTransport (Iso.refl (fiberFunctor s hs)) G x = x := rfl

theorem groupPathTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (G : Grp (Over S))
    [IsFinite G.X.hom] [Etale G.X.hom] (x : Additive (Over.mk s ⟶ G.X)) :
    groupPathTransport (p ≪≫ q) G x =
      groupPathTransport q G (groupPathTransport p G x) := rfl

theorem groupPathTransport_monodromy (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (G : Grp (Over S)) [IsFinite G.X.hom] [Etale G.X.hom]
    (g : FundamentalGroup s hs) (x : Additive (Over.mk s ⟶ G.X)) :
    groupPathTransport p G (groupMonodromy s hs G g x) =
      groupMonodromy t ht G (pathConjugation p g) (groupPathTransport p G x) := by
  change p.hom.app (ofOver G.X) (g.hom.app (ofOver G.X) x) =
    p.hom.app (ofOver G.X) (g.hom.app (ofOver G.X)
      (p.inv.app (ofOver G.X) (p.hom.app (ofOver G.X) x)))
  have hx : p.inv.app (ofOver G.X) (p.hom.app (ofOver G.X) x) = x :=
    ConcreteCategory.congr_hom (p.hom_inv_id_app (ofOver G.X)) x
  rw [hx]

end Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.GroupScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)
  [IsFinite (kernel (multiplication G n)).X.hom]
  [Etale (kernel (multiplication G n)).X.hom]

/-- Evaluate a path on the actual torsion cover and use the existing kernel-point equivalences. -/
def finiteLevelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level G (Over.mk s) n ≃+ Level G (Over.mk t) n :=
  ((kernelLevelEquiv G (Over.mk s) n).symm.trans
    (groupPathTransport p (kernel (multiplication G n)))).trans
      (kernelLevelEquiv G (Over.mk t) n)

@[simp] theorem finiteLevelTransport_kernel (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Additive (Over.mk s ⟶ (kernel (multiplication G n)).X)) :
    finiteLevelTransport G n p (kernelLevelEquiv G (Over.mk s) n x) =
      kernelLevelEquiv G (Over.mk t) n
        (Additive.ofMul (pathAct p (kernel (multiplication G n)).X x.toMul)) := by
  simp [finiteLevelTransport, groupPathTransport]

@[simp] theorem finiteLevelTransport_refl (x : Level G (Over.mk s) n) :
    finiteLevelTransport G n (Iso.refl (fiberFunctor s hs)) x = x := by
  simp [finiteLevelTransport, groupPathTransport, pathAct]

theorem finiteLevelTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Level G (Over.mk s) n) :
    finiteLevelTransport G n (p ≪≫ q) x =
      finiteLevelTransport G n q (finiteLevelTransport G n p x) := by
  simp only [finiteLevelTransport, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

theorem finiteLevelTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (finiteLevelTransport G n p).symm = finiteLevelTransport G n p.symm := rfl

/-- A path that is an automorphism gives exactly the existing geometric monodromy. -/
theorem finiteLevelTransport_aut (g : FundamentalGroup s hs) :
    finiteLevelTransport G n g = finiteLevelMonodromy G s hs n g := rfl

theorem continuous_finiteLevelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (finiteLevelTransport G n p) := continuous_of_discreteTopology

theorem finiteLevelTransport_zmod_smul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ZMod n) (x : Level G (Over.mk s) n) :
    finiteLevelTransport G n p (a • x) = a • finiteLevelTransport G n p x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

theorem finiteLevelTransport_monodromy (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Level G (Over.mk s) n) :
    finiteLevelTransport G n p (finiteLevelMonodromy G s hs n g x) =
      finiteLevelMonodromy G t ht n (pathConjugation p g)
        (finiteLevelTransport G n p x) := by
  simp only [finiteLevelTransport, finiteLevelMonodromy, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  rw [groupPathTransport_monodromy]

/-- The difference between two paths acts by target-point monodromy. -/
theorem finiteLevelTransport_change_path (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level G (Over.mk s) n) :
    finiteLevelTransport G n q x =
      finiteLevelMonodromy G t ht n (p.symm ≪≫ q) (finiteLevelTransport G n p x) := by
  rw [← finiteLevelTransport_aut, ← finiteLevelTransport_trans]
  simp

variable {n}

theorem finiteLevelTransport_transition {m : ℕ}
    [IsFinite (kernel (multiplication G m)).X.hom]
    [Etale (kernel (multiplication G m)).X.hom]
    (h : n ∣ m) (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level G (Over.mk s) m) :
    finiteLevelTransport G n p (transition G (Over.mk s) h x) =
      transition G (Over.mk t) h (finiteLevelTransport G m p x) := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv G (Over.mk s) m).surjective x
  rw [← kernelLevelEquiv_transition, finiteLevelTransport_kernel,
    finiteLevelTransport_kernel, ← kernelLevelEquiv_transition]
  congr 1
  exact pathAct_naturality p (kernelTransition G h) y.toMul

theorem finiteLevelTransport_map {H : Grp (Over S)} [IsCommMonObj H.X]
    [IsFinite (kernel (multiplication H n)).X.hom]
    [Etale (kernel (multiplication H n)).X.hom]
    (f : G ⟶ H) (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level G (Over.mk s) n) :
    finiteLevelTransport H n p (levelMap (Over.mk s) f n x) =
      levelMap (Over.mk t) f n (finiteLevelTransport G n p x) := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv G (Over.mk s) n).surjective x
  rw [← kernelLevelEquiv_map, finiteLevelTransport_kernel,
    finiteLevelTransport_kernel, ← kernelLevelEquiv_map]
  congr 1
  exact pathAct_naturality p (kernelLevelMap f n) y.toMul

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤)))

/-- Path transport on an actual positive, invertible torsion level. -/
def levelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level A (Over.mk s) n ≃+ Level A (Over.mk t) n := by
  letI := torsionKernel_isFinite htor A n hn hu
  letI := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport A.toGrp n p

/-- Transport evaluates the path on the actual torsion cover. -/
theorem levelTransport_kernel (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Additive (Over.mk s ⟶ (GroupScheme.kernel
      (GroupScheme.multiplication A.toGrp n)).X)) :
    levelTransport htor A n hn hu p (kernelLevelEquiv A (Over.mk s) n x) =
      kernelLevelEquiv A (Over.mk t) n
        (Additive.ofMul (p.hom.app (torsionCover htor A n hn hu) x.toMul)) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_kernel A.toGrp n p x

@[simp] theorem levelTransport_refl (x : Level A (Over.mk s) n) :
    levelTransport htor A n hn hu (Iso.refl (fiberFunctor s hs)) x = x := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_refl A.toGrp n x

theorem levelTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Level A (Over.mk s) n) :
    levelTransport htor A n hn hu (p ≪≫ q) x =
      levelTransport htor A n hn hu q (levelTransport htor A n hn hu p x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_trans A.toGrp n p q x

theorem levelTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (levelTransport htor A n hn hu p).symm = levelTransport htor A n hn hu p.symm := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_symm A.toGrp n p

theorem levelTransport_aut (g : FundamentalGroup s hs) :
    levelTransport htor A n hn hu g = levelMonodromy s hs htor A n hn hu g := rfl

theorem continuous_levelTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (levelTransport htor A n hn hu p) := continuous_of_discreteTopology

theorem levelTransport_zmod_smul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ZMod n) (x : Level A (Over.mk s) n) :
    levelTransport htor A n hn hu p (a • x) = a • levelTransport htor A n hn hu p x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

/-- Equivariance uses the conjugation isomorphism determined by the same path. -/
theorem levelTransport_monodromy (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Level A (Over.mk s) n) :
    levelTransport htor A n hn hu p (levelMonodromy s hs htor A n hn hu g x) =
      levelMonodromy t ht htor A n hn hu (pathConjugation p g)
        (levelTransport htor A n hn hu p x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_monodromy A.toGrp n p g x

/-- Changing the path changes transport by target-point monodromy. -/
theorem levelTransport_change_path (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level A (Over.mk s) n) :
    levelTransport htor A n hn hu q x =
      levelMonodromy t ht htor A n hn hu (p.symm ≪≫ q)
        (levelTransport htor A n hn hu p x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_change_path A.toGrp n p q x

/-- Transport commutes with the existing divisibility transition. -/
theorem levelTransport_transition (m : ℕ) (hm : 0 < m)
    (hu_m : IsUnit (m : Γ(S, ⊤))) (h : n ∣ m)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Level A (Over.mk s) m) :
    levelTransport htor A n hn hu p (transition A (Over.mk s) h x) =
      transition A (Over.mk t) h (levelTransport htor A m hm hu_m p x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have := torsionKernel_isFinite htor A m hm hu_m
  have := torsionKernel_etale htor A m hm hu_m
  exact GroupScheme.Tate.finiteLevelTransport_transition A.toGrp h p x

/-- Transport is natural in an actual abelian-scheme homomorphism. -/
theorem levelTransport_map {B : AbelianScheme S} (f : A ⟶ B)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Level A (Over.mk s) n) :
    levelTransport htor B n hn hu p (levelMap (Over.mk s) f n x) =
      levelMap (Over.mk t) f n (levelTransport htor A n hn hu p x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have := torsionKernel_isFinite htor B n hn hu
  have := torsionKernel_etale htor B n hn hu
  exact GroupScheme.Tate.finiteLevelTransport_map A.toGrp (AbelianScheme.groupHom f) p x

end Langlands.AbelianScheme.Tate
