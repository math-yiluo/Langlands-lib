import Langlands.Geometry.FormalGroup.PDivisibleGroupMorphisms
import Langlands.GroupScheme.HomScheme.MultiplicativeTargetEtale
import Langlands.AbelianScheme.RationalBaseChange

/-! # Base change of actual p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

open GroupScheme GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local notation "R₀" => CommRingCat.of R
local notation "S₀" => CommRingCat.of S
local notation "b" => specBase R S

local instance restrictAffineAlgebraInstance (A : CommAlgCat.{u} S) : Algebra R A :=
  Algebra.compHom A (algebraMap R S)

local instance restrictAffineScalarTower (A : CommAlgCat.{u} S) : IsScalarTower R S A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- An affine coefficient test over the new base, regarded as an algebra over the old base. -/
def restrictAffineAlgebra (A : CommAlgCat.{u} S) : CommAlgCat.{u} R :=
  CommAlgCat.of R A

/-- Regard an actual morphism of test algebras as a morphism over the old base. -/
def restrictAffineMap {A B : CommAlgCat.{u} S} (φ : A ⟶ B) :
    restrictAffineAlgebra (R := R) A ⟶ restrictAffineAlgebra (R := R) B :=
  CommAlgCat.ofHom (φ.hom.restrictScalars R)

private def restrictAffineTestIso (A : CommAlgCat.{u} S) :
    (Over.map b).obj (affineTest (R := S₀) A) ≅
      affineTest (R := R₀) (restrictAffineAlgebra (R := R) A) :=
  specOverIso (R := R) (R' := S) A

/-- Points of the actual base change on an affine test are points of the original
scheme on its restriction of scalars. -/
def baseChangeAffinePoints (G : CommGroupScheme (Spec R₀)) (A : CommAlgCat.{u} S) :
    (affineTest (R := S₀) A ⟶ ((CommGroupScheme.baseChange b).obj G).X) ≃*
      (affineTest (R := R₀) (restrictAffineAlgebra (R := R) A) ⟶ G.X) :=
  let e := restrictAffineTestIso (R := R) A
  (baseChangePointsEquiv b G.toGrp (affineTest (R := S₀) A)).trans {
    toFun x := e.inv ≫ x
    invFun x := e.hom ≫ x
    left_inv x := by simp [← Category.assoc]
    right_inv x := by simp [← Category.assoc]
    map_mul' x y := MonObj.comp_mul _ _ _ }

/-- The point identification intertwines the two actual group scheme maps. -/
theorem baseChangeAffinePoints_comp {G H : CommGroupScheme (Spec R₀)} (f : G ⟶ H)
    (A : CommAlgCat.{u} S) (x : affineTest (R := S₀) A ⟶ ((CommGroupScheme.baseChange b).obj G).X) :
    let f' : ((CommGroupScheme.baseChange b).obj G).X ⟶ ((CommGroupScheme.baseChange b).obj H).X :=
      ((CommGroupScheme.baseChange b).map f).toMul.hom.hom
    baseChangeAffinePoints (R := R) (S := S) H A (x ≫ f') =
      baseChangeAffinePoints (R := R) (S := S) G A x ≫ f.toMul.hom.hom := by
  let e := restrictAffineTestIso (R := R) A
  let T := affineTest (R := S₀) A
  change e.inv ≫ baseChangePointsEquiv b H.toGrp T
    (x ≫ ((CommGroupScheme.baseChange b).map f).toMul.hom.hom) =
      (e.inv ≫ baseChangePointsEquiv b G.toGrp T x) ≫ f.toMul.hom.hom
  exact (congrArg (fun t => e.inv ≫ t) (baseChangePointsEquiv_comp b f.toMul T x)).trans
    (Category.assoc _ _ _).symm

/-- Restricting the coefficient homomorphism gives the actual map on the old affine tests. -/
theorem baseChangeAffinePoints_naturality (G : CommGroupScheme (Spec R₀)) {A B : CommAlgCat.{u} S}
    (φ : A ⟶ B) (x : affineTest (R := S₀) A ⟶ ((CommGroupScheme.baseChange b).obj G).X) :
    let c : affineTest (R := S₀) B ⟶ affineTest (R := S₀) A := (algSpec S₀).map φ.op
    baseChangeAffinePoints (R := R) (S := S) G B (c ≫ x) =
      (algSpec R₀).map (restrictAffineMap (R := R) φ).op ≫ baseChangeAffinePoints (R := R) (S := S) G A x := by
  let e := restrictAffineTestIso (R := R) A
  let f := restrictAffineTestIso (R := R) B
  let c := (algSpec S₀).map φ.op
  let d := (algSpec R₀).map (restrictAffineMap (R := R) φ).op
  let t := baseChangePointsEquiv b G.toGrp (affineTest (R := S₀) A) x
  have h : (Over.map b).map c ≫ e.hom = f.hom ≫ d :=
    specOverIso_naturality (R := R) (R' := S) φ.hom
  have hd : f.inv ≫ (Over.map b).map c = d ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]
  calc
    _ = f.inv ≫ ((Over.map b).map c ≫ t) :=
      congrArg (fun z => f.inv ≫ z) (baseChangePointsEquiv_naturality b G.toGrp c x)
    _ = _ := by
      change f.inv ≫ ((Over.map b).map c ≫ t) = d ≫ e.inv ≫ t
      rw [← Category.assoc, hd, Category.assoc]

/-- Affine fppf exactness is preserved by arbitrary pullback of the coefficient ring. -/
theorem AffineFppfShortExact.baseChange {G H J : CommGroupScheme (Spec R₀)}
    {i : G ⟶ H} {q : H ⟶ J} (h : AffineFppfShortExact i q) :
    AffineFppfShortExact ((CommGroupScheme.baseChange b).map i) ((CommGroupScheme.baseChange b).map q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A x y hxy
    apply (baseChangeAffinePoints G A).injective
    apply h.1 (restrictAffineAlgebra (R := R) A)
    have hh := congrArg (baseChangeAffinePoints H A) hxy
    rwa [baseChangeAffinePoints_comp, baseChangeAffinePoints_comp] at hh
  · intro A x
    let eG := baseChangeAffinePoints G A
    let eH := baseChangeAffinePoints H A
    let eJ := baseChangeAffinePoints J A
    have hker : x ≫ ((CommGroupScheme.baseChange b).map q).toMul.hom.hom = 1 ↔
        eH x ≫ q.toMul.hom.hom = 1 := by
      rw [← eJ.injective.eq_iff]
      exact (congrArg₂ (· = ·) (baseChangeAffinePoints_comp q A x) (map_one eJ)).to_iff
    rw [hker, h.2.1 (restrictAffineAlgebra (R := R) A) (eH x)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨eG.symm y, eH.injective ?_⟩
      change baseChangeAffinePoints H A (_ ≫ ((CommGroupScheme.baseChange b).map i).toMul.hom.hom) = eH x
      rw [baseChangeAffinePoints_comp]
      change eG (eG.symm y) ≫ i.toMul.hom.hom = eH x
      rw [MulEquiv.apply_symm_apply, hy]
    · rintro ⟨y, hy⟩
      exact ⟨eG y, (baseChangeAffinePoints_comp i A y).symm.trans (congrArg eH hy)⟩
  · intro A y
    let A₀ := restrictAffineAlgebra (R := R) A
    let y₀ := baseChangeAffinePoints J A y
    obtain ⟨B, φ, hflat, hfp, x, hx⟩ := h.2.2 A₀ y₀
    let : Algebra S B := (φ.hom.toRingHom.comp (algebraMap S A)).toAlgebra
    let C := CommAlgCat.of S B
    let ψ : A ⟶ C := CommAlgCat.ofHom { __ := φ.hom.toRingHom, commutes' := fun _ => rfl }
    let δ : B ⟶ restrictAffineAlgebra (R := R) C := CommAlgCat.ofHom
      { __ := RingHom.id B, commutes' := fun r => (φ.hom.commutes r).symm }
    have hδ : φ ≫ δ = restrictAffineMap (R := R) ψ := by
      apply CommAlgCat.hom_ext
      exact AlgHom.ext fun _ => rfl
    let x₀ := (algSpec R₀).map δ.op ≫ x
    let e := baseChangeAffinePoints H C
    refine ⟨C, ψ, hflat, hfp, e.symm x₀, (baseChangeAffinePoints J C).injective ?_⟩
    rw [baseChangeAffinePoints_comp, baseChangeAffinePoints_naturality]
    change e (e.symm x₀) ≫ q.toMul.hom.hom =
      (algSpec R₀).map (restrictAffineMap (R := R) ψ).op ≫ y₀
    rw [MulEquiv.apply_symm_apply]
    change ((algSpec R₀).map δ.op ≫ x) ≫ q.toMul.hom.hom = _
    rw [Category.assoc, hx, ← Category.assoc, ← (algSpec R₀).map_comp, ← op_comp, hδ]

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

open CommGroupScheme GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {p : ℕ} [Fact p.Prime]

/-- The actual pullback of each finite group scheme, with the same scalar and
short exact sequence relations after base change. -/
def baseChange (G : PDivisibleGroup (CommRingCat.of R) p) : PDivisibleGroup (CommRingCat.of S) p where
  inclusions := G.inclusions ⋙ CommGroupScheme.baseChange (specBase R S)
  transfer i := (CommGroupScheme.baseChange (specBase R S)).map (G.transfer i)
  transfer_id n := by
    rw [G.transfer_id]
    exact (CommGroupScheme.baseChange (specBase R S)).map_id (G.inclusions.obj n)
  transfer_comp i j := by rw [G.transfer_comp, Functor.map_comp]
  finiteLocallyFree n := by
    let b := specBase R S
    let f := (G.inclusions.obj n).X.hom
    obtain ⟨hfin, hflat, hfp⟩ := G.finiteLocallyFree n
    change IsFinite (pullback.snd f b) ∧ Flat (pullback.snd f b) ∧ LocallyOfFinitePresentation (pullback.snd f b)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  multiplication {m n} i := by
    let B := CommGroupScheme.baseChange (specBase R S)
    change B.map (G.transfer i) ≫ B.map (G.inclusions.map i) =
      p ^ (n - m) • 𝟙 (B.obj (G.inclusions.obj n))
    rw [← B.map_comp, G.multiplication, Functor.map_nsmul, B.map_id]
  shortExact m n := (G.shortExact m n).baseChange (S := S)

/-- Base change maps each actual level map to its scheme-theoretic pullback. -/
def Hom.baseChangeMap {G H : PDivisibleGroup (CommRingCat.of R) p} (f : G ⟶ H) :
    G.baseChange (S := S) ⟶ H.baseChange (S := S) :=
  let B := CommGroupScheme.baseChange (specBase R S)
  Hom.ofComponents (fun n => B.map (f.app n)) (by
    intro m n i
    change B.map (G.inclusions.map i) ≫ B.map (f.app n) =
      B.map (f.app m) ≫ B.map (H.inclusions.map i)
    rw [← B.map_comp, ← B.map_comp, f.naturality]) (by
    intro m n i
    change B.map (G.transfer i) ≫ B.map (f.app m) =
      B.map (f.app n) ≫ B.map (H.transfer i)
    rw [← B.map_comp, ← B.map_comp, f.transfer_naturality])

@[simp] theorem Hom.baseChangeMap_app {G H : PDivisibleGroup (CommRingCat.of R) p} (f : G ⟶ H) (n : ℕ) :
    (f.baseChangeMap (S := S)).app n = (CommGroupScheme.baseChange (specBase R S)).map (f.app n) :=
  rfl

/-- The scheme-theoretic pullback of the tower is an additive functor. -/
def baseChangeFunctor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) [Fact p.Prime] :
    PDivisibleGroup (CommRingCat.of R) p ⥤ PDivisibleGroup (CommRingCat.of S) p where
  obj G := G.baseChange
  map f := f.baseChangeMap
  map_id G := Hom.ext fun n => (CommGroupScheme.baseChange (specBase R S)).map_id (G.inclusions.obj n)
  map_comp f g := Hom.ext fun n =>
    (CommGroupScheme.baseChange (specBase R S)).map_comp (f.app n) (g.app n)

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) [Fact p.Prime] :
    (baseChangeFunctor R S p).Additive where
  map_add {_ _ f g} := Hom.ext fun n =>
    (CommGroupScheme.baseChange (specBase R S)).map_add (f := f.app n) (g := g.app n)

end Langlands.PDivisibleGroup
