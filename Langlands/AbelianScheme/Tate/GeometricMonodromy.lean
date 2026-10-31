import Langlands.AbelianScheme.Tate.IntegralMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Geometric Tate representations from proved finite étale geometry -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate.Geometric

universe u
open Langlands.AlgebraicGeometry
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The existing geometric-fibre automorphism group, using proved fibre finiteness. -/
abbrev FundamentalGroup :=
  FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)

variable (A : AbelianScheme S) (n : ℕ) (hn : 0 < n)
  (hu : IsUnit (n : Γ(S, ⊤)))

/-- Actual geometric monodromy as a residue-linear representation. -/
def levelRepresentation :
    FundamentalGroup s →*
      (Level A (Over.mk s) n ≃ₗ[ZMod n] Level A (Over.mk s) n) where
  toFun g :=
    { levelMonodromy s (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu g with
      map_smul' := levelMonodromy_zmod_smul s
        (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu g }
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact levelMonodromy_one s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact levelMonodromy_mul s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu g h x

/-- The representation is evaluation on the actual multiplication-kernel fibre. -/
theorem levelRepresentation_kernel (g : FundamentalGroup s)
    (x : Additive (Over.mk s ⟶
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X)) :
    levelRepresentation s A n hn hu g (kernelLevelEquiv A (Over.mk s) n x) =
      kernelLevelEquiv A (Over.mk s) n
        (Additive.ofMul
          (g.hom.app (torsionCover torsionFiniteEtale A n hn hu) x.toMul)) :=
  levelMonodromy_kernel s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu g x

include hn hu in
/-- Finiteness of the actual positive invertible geometric torsion level. -/
theorem levelFinite : Finite (Level A (Over.mk s) n) :=
  level_finite s (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu

/-- Joint continuity uses the existing evaluation and discrete torsion topologies. -/
theorem continuous_levelRepresentation :
    Continuous (fun z : FundamentalGroup s × Level A (Over.mk s) n =>
      levelRepresentation s A n hn hu z.1 z.2) :=
  continuous_levelMonodromy s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu

/-- The existing divisibility transition intertwines the finite representations. -/
theorem levelRepresentation_transition (m : ℕ) (hm : 0 < m)
    (hu_m : IsUnit (m : Γ(S, ⊤))) (h : n ∣ m)
    (g : FundamentalGroup s) (x : Level A (Over.mk s) m) :
    levelRepresentation s A n hn hu g (transition A (Over.mk s) h x) =
      transition A (Over.mk s) h (levelRepresentation s A m hm hu_m g x) :=
  levelMonodromy_transition s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu m hm hu_m h g x

/-- Actual homomorphisms intertwine the finite representations. -/
theorem levelRepresentation_map {B : AbelianScheme S} (f : A ⟶ B)
    (g : FundamentalGroup s) (x : Level A (Over.mk s) n) :
    levelRepresentation s B n hn hu g (levelMap (Over.mk s) f n x) =
      levelMap (Over.mk s) f n (levelRepresentation s A n hn hu g x) :=
  levelMonodromy_map s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A n hn hu f g x

variable (P : ℕ → Prop) (hunit : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- The actual selected Tate limit as a representation over the profinite integers. -/
def integralRepresentation :
    FundamentalGroup s →*
      (Integral A (Over.mk s) P ≃ₗ[Global.ProfiniteIntegerRing]
        Integral A (Over.mk s) P) where
  toFun := integralMonodromyLinearEquiv s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_one s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_mul s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit g h x

/-- Every selected coordinate is the finite representation on the same torsion section. -/
@[simp] theorem evaluation_integralRepresentation (g : FundamentalGroup s)
    (n : Index P) (x : Integral A (Over.mk s) P) :
    evaluation A (Over.mk s) P n (integralRepresentation s A P hunit g x) =
      levelRepresentation s A n.val n.property.1 (hunit n) g
        (evaluation A (Over.mk s) P n x) := rfl

/-- Joint continuity for the existing integral Tate topology. -/
theorem continuous_integralRepresentation :
    Continuous (fun z : FundamentalGroup s × Integral A (Over.mk s) P =>
      integralRepresentation s A P hunit z.1 z.2) :=
  continuous_integralMonodromy s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit

/-- The selected integral action, available for local installation. -/
@[instance_reducible] def integralAction :
    DistribMulAction (FundamentalGroup s) (Integral A (Over.mk s) P) :=
  integralMonodromyAction s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit

@[simp] theorem integralAction_smul (g : FundamentalGroup s)
    (x : Integral A (Over.mk s) P) :
    letI := integralAction s A P hunit
    g • x = integralRepresentation s A P hunit g x := rfl

theorem integralAction_continuousSMul :
    letI := integralAction s A P hunit
    ContinuousSMul (FundamentalGroup s) (Integral A (Over.mk s) P) :=
  integralMonodromyAction_continuousSMul s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit

/-- The actual integral Tate map is equivariant without a supplied geometric action. -/
theorem integralRepresentation_map {B : AbelianScheme S} (f : A ⟶ B)
    (g : FundamentalGroup s) (x : Integral A (Over.mk s) P) :
    integralRepresentation s B P hunit g (map (Over.mk s) P f x) =
      map (Over.mk s) P f (integralRepresentation s A P hunit g x) :=
  integralMonodromy_map s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale P hunit f g x

include hunit in
/-- Compactness follows from the proved geometric finiteness at each selected order. -/
theorem integralCompactSpace : CompactSpace (Integral A (Over.mk s) P) :=
  integralMonodromy_compactSpace s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit

/-- The existing selected integral Tate space bundled as a profinite space. -/
def profiniteTate : Profinite :=
  geometricProfiniteTate s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit

variable {A}

/-- The published map of actual Tate families, bundled using proved geometric finiteness. -/
def profiniteTateMap {B : AbelianScheme S} (f : A ⟶ B) :
    profiniteTate s A P hunit ⟶ profiniteTate s B P hunit := by
  letI : ∀ n : Index P, Finite (Level A (Over.mk s) n.val) :=
    fun n => levelFinite s A n.val n.property.1 (hunit n)
  letI : ∀ n : Index P, Finite (Level B (Over.mk s) n.val) :=
    fun n => levelFinite s B n.val n.property.1 (hunit n)
  exact GroupScheme.Tate.profiniteMap (Over.mk s) P (AbelianScheme.groupHom f)

@[simp] theorem profiniteTateMap_apply {B : AbelianScheme S} (f : A ⟶ B)
    (x : Integral A (Over.mk s) P) :
    profiniteTateMap s P hunit f x = map (Over.mk s) P f x := rfl

/-- The map sends each actual torsion section to its image under the homomorphism. -/
@[simp] theorem evaluation_profiniteTateMap {B : AbelianScheme S} (f : A ⟶ B)
    (n : Index P) (x : Integral A (Over.mk s) P) :
    evaluation B (Over.mk s) P n (profiniteTateMap s P hunit f x) =
      levelMap (Over.mk s) f n.val (evaluation A (Over.mk s) P n x) :=
  evaluation_map (Over.mk s) P f n x

@[simp] theorem profiniteTateMap_id :
    profiniteTateMap s P hunit (𝟙 A) = 𝟙 (profiniteTate s A P hunit) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact DFunLike.congr_fun (map_id (Over.mk s) P) x

theorem profiniteTateMap_comp {B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    profiniteTateMap s P hunit (f ≫ g) =
      profiniteTateMap s P hunit f ≫ profiniteTateMap s P hunit g := by
  apply ConcreteCategory.hom_ext
  intro x
  exact DFunLike.congr_fun (map_comp (Over.mk s) P f g) x

/-- The actual geometric Tate-space functor on abelian schemes over the fixed base. -/
def profiniteTateFunctor : AbelianScheme S ⥤ Profinite where
  obj A := profiniteTate s A P hunit
  map f := profiniteTateMap s P hunit f
  map_id _ := profiniteTateMap_id s P hunit
  map_comp f g := profiniteTateMap_comp s P hunit f g

/-- The profinite-space morphisms intertwine the constructed integral representation. -/
theorem profiniteTateMap_equivariant {B : AbelianScheme S} (f : A ⟶ B)
    (g : FundamentalGroup s) (x : Integral A (Over.mk s) P) :
    integralRepresentation s B P hunit g (profiniteTateMap s P hunit f x) =
      profiniteTateMap s P hunit f (integralRepresentation s A P hunit g x) :=
  integralRepresentation_map s A P hunit f g x

variable (A)

/-- Full integral representation; every positive torsion order is required to be a unit. -/
abbrev fullRepresentation
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :=
  integralRepresentation s A (fun _ => True) hu

/-- Away representation over the existing away profinite-integer scalar ring. -/
def awayRepresentation (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :
    FundamentalGroup s →*
      (AwayAt A s m ≃ₗ[Global.PrimeToProfiniteIntegerRing m] AwayAt A s m) where
  toFun := awayMonodromyLinearEquiv s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A m hu
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_one s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A _ hu x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_mul s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A _ hu g h x

/-- Full-to-away restriction intertwines these representations. -/
theorem restrictAway_representation (m : ℕ)
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s) (x : FullAt A s) :
    restrictAway A (Over.mk s) m (fullRepresentation s A hu g x) =
      awayRepresentation s A m (fun n => hu ⟨n.val, n.property.1, trivial⟩) g
        (restrictAway A (Over.mk s) m x) := rfl

/-- Full Tate-space functor with the full invertibility hypothesis. -/
abbrev fullProfiniteTateFunctor
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :=
  profiniteTateFunctor s (fun _ => True) hu

/-- Away Tate-space functor with invertibility only at the retained orders. -/
abbrev awayProfiniteTateFunctor (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) :=
  profiniteTateFunctor s (fun n => Nat.Coprime n m) hu

end Langlands.AbelianScheme.Tate.Geometric
