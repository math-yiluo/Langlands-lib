import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.Products
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.SmoothProducts

/-! # Split tori over an arbitrary base -/

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-! ### Isomorphisms and points -/

/-- A group-scheme isomorphism identifies the groups of points on every test scheme. -/
def isoPointsEquiv {G H : GroupScheme S} (e : G ≅ H) (T : Over S) :
    (T ⟶ G.X) ≃* (T ⟶ H.X) :=
  ((yonedaGrp.mapIso e).app (op T)).groupIsoToMulEquiv

@[simp] theorem isoPointsEquiv_apply {G H : GroupScheme S} (e : G ≅ H) (T : Over S)
    (x : T ⟶ G.X) : isoPointsEquiv e T x = x ≫ e.hom.hom.hom := rfl

section PointModels

variable {G H : GroupScheme S} (M : Over S → Type v) [∀ T, Group (M T)]
  (res : ∀ {T T' : Over S}, (T' ⟶ T) → M T →* M T')
  (eG : ∀ T, (T ⟶ G.X) ≃* M T) (eH : ∀ T, (T ⟶ H.X) ≃* M T)
  (hG : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), eG T' (a ≫ x) = res a (eG T x))
  (hH : ∀ {T T' : Over S} (a : T' ⟶ T) (y : T ⟶ H.X), eH T' (a ≫ y) = res a (eH T y))

include hG hH in
theorem isoOfPointModels_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X) :
    ((eG T').trans (eH T').symm) (a ≫ x) = a ≫ ((eG T).trans (eH T).symm) x := by
  apply (eH T').injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hG, hH]

/-- Two group schemes with the same natural model of their point groups are isomorphic. -/
def isoOfPointModels : G ≅ H :=
  isoOfPoints (fun T => (eG T).trans (eH T).symm)
    (isoOfPointModels_naturality M res eG eH hG hH)

/-- The isomorphism built from point models is the identity on the models. -/
theorem isoOfPointModels_hom (T : Over S) (x : T ⟶ G.X) :
    eH T (x ≫ (isoOfPointModels M res eG eH hG hH).hom.hom.hom) = eG T x := by
  have key := comp_isoOfPoints_hom (fun T => (eG T).trans (eH T).symm)
    (isoOfPointModels_naturality M res eG eH hG hH) T x
  rw [isoOfPointModels, key]
  simp

/-- The inverse isomorphism built from point models is the identity on the models. -/
theorem isoOfPointModels_inv (T : Over S) (y : T ⟶ H.X) :
    eG T (y ≫ (isoOfPointModels M res eG eH hG hH).inv.hom.hom) = eH T y := by
  have key := comp_isoOfPoints_inv (fun T => (eG T).trans (eH T).symm)
    (isoOfPointModels_naturality M res eG eH hG hH) T y
  rw [isoOfPointModels, key]
  simp

end PointModels

/-! ### Split tori -/

/-- The split torus `𝔾_m^I` over `S`, for a finite index type `I`: the categorical finite
product of copies of the actual multiplicative group scheme. -/
abbrev splitTorus (S : Scheme.{u}) (I : Type u) [Finite I] : GroupScheme S :=
  pi fun _ : I => (Gm S).toGrp

namespace splitTorus

variable (I : Type u) [Finite I]

/-- Restriction of families of global units along a morphism of test schemes. -/
abbrev unitsRestrict {T T' : Over S} (a : T' ⟶ T) :
    (I → (Γ(T.left, ⊤))ˣ) →* (I → (Γ(T'.left, ⊤))ˣ) :=
  (Units.map a.left.appTop.hom.toMonoidHom).compLeft I

/-- Points of the split torus are families, indexed by `I`, of global units. -/
def pointsEquiv (T : Over S) : (T ⟶ (splitTorus S I).X) ≃* (I → (Γ(T.left, ⊤))ˣ) :=
  (piPointsEquiv _ T).trans (MulEquiv.piCongrRight fun _ => Gm.pointsEquiv S T)

theorem pointsEquiv_apply (T : Over S) (x : T ⟶ (splitTorus S I).X) (i : I) :
    pointsEquiv I T x i = Gm.pointsEquiv S T (x ≫ (Pi.π (fun _ : I => (Gm S).toGrp) i).hom.hom) :=
  rfl

/-- The point model of the split torus is natural in the test scheme. -/
theorem pointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (splitTorus S I).X) :
    pointsEquiv I T' (a ≫ x) = unitsRestrict I a (pointsEquiv I T x) := by
  funext i
  rw [pointsEquiv_apply, Category.assoc, Gm.pointsEquiv_naturality]
  rfl

/-- Points over an affine test scheme `Spec R ⟶ S` are families of units of `R`. -/
def affinePointsEquiv {R : CommRingCat.{u}} (f : Spec R ⟶ S) :
    (Over.mk f ⟶ (splitTorus S I).X) ≃* (I → Rˣ) :=
  (piPointsEquiv _ _).trans (MulEquiv.piCongrRight fun _ => Gm.affinePointsEquiv f)

end splitTorus

/-- A group scheme over `S` is a split torus if it is isomorphic, as a group scheme over `S`,
to `splitTorus S I` for some finite index type `I`. -/
def IsSplitTorus (G : GroupScheme S) : Prop :=
  ∃ (I : Type u) (_ : Finite I), Nonempty (G ≅ splitTorus S I)

theorem IsSplitTorus.of_iso {G H : GroupScheme S} (e : G ≅ H) (h : IsSplitTorus H) :
    IsSplitTorus G := by
  obtain ⟨I, hI, ⟨f⟩⟩ := h
  exact ⟨I, hI, ⟨e ≪≫ f⟩⟩

theorem IsSplitTorus.iso_iff {G H : GroupScheme S} (e : G ≅ H) :
    IsSplitTorus G ↔ IsSplitTorus H :=
  ⟨IsSplitTorus.of_iso e.symm, IsSplitTorus.of_iso e⟩

theorem isSplitTorus_splitTorus (I : Type u) [Finite I] : IsSplitTorus (splitTorus S I) :=
  ⟨I, inferInstance, ⟨Iso.refl _⟩⟩

namespace splitTorus

/-- `𝔾_m` is the split torus of rank one. -/
def gmIso (S : Scheme.{u}) : (Gm S).toGrp ≅ splitTorus S PUnit :=
  isoOfPointModels (fun T : Over S => PUnit → (Γ(T.left, ⊤))ˣ)
    (fun a => unitsRestrict PUnit a)
    (fun T => (Gm.pointsEquiv S T).trans
      (MulEquiv.piUnique fun _ : PUnit => (Γ(T.left, ⊤))ˣ).symm)
    (fun T => pointsEquiv PUnit T)
    (fun a x => by
      funext i
      change Gm.pointsEquiv S _ (a ≫ x) = _
      rw [Gm.pointsEquiv_naturality]
      rfl)
    (fun a y => pointsEquiv_naturality PUnit a y)

variable (I J : Type u) [Finite I] [Finite J]

/-- Families on a sum are pairs of families, multiplicatively. -/
def sumArrowMulEquiv (M : Type v) [Group M] : (I ⊕ J → M) ≃* (I → M) × (J → M) where
  __ := Equiv.sumArrowEquivProdArrow I J M
  map_mul' _ _ := rfl

/-- The point model of a binary product of split tori. -/
def prodPointsEquiv (T : Over S) :
    (T ⟶ (splitTorus S I ⊗ splitTorus S J).X) ≃* (I ⊕ J → (Γ(T.left, ⊤))ˣ) :=
  (productPointsEquiv _ _ T).trans
    (((pointsEquiv I T).prodCongr (pointsEquiv J T)).trans (sumArrowMulEquiv I J _).symm)

theorem prodPointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus S I ⊗ splitTorus S J).X) :
    prodPointsEquiv I J T' (a ≫ x) = unitsRestrict (I ⊕ J) a (prodPointsEquiv I J T x) := by
  funext k
  rcases k with i | j
  · change pointsEquiv I T' ((a ≫ x) ≫ fst _ _) i = _
    rw [Category.assoc, pointsEquiv_naturality]
    rfl
  · change pointsEquiv J T' ((a ≫ x) ≫ snd _ _) j = _
    rw [Category.assoc, pointsEquiv_naturality]
    rfl

/-- The product of split tori on `I` and `J` is the split torus on `I ⊕ J`. -/
def prodIso : splitTorus S I ⊗ splitTorus S J ≅ splitTorus S (I ⊕ J) :=
  isoOfPointModels (fun T : Over S => I ⊕ J → (Γ(T.left, ⊤))ˣ)
    (fun a => unitsRestrict (I ⊕ J) a) (prodPointsEquiv I J) (pointsEquiv (I ⊕ J))
    (fun a x => prodPointsEquiv_naturality I J a x)
    (fun a y => pointsEquiv_naturality (I ⊕ J) a y)

end splitTorus

/-- The multiplicative group scheme is a split torus. -/
theorem isSplitTorus_gm : IsSplitTorus (Gm S).toGrp :=
  ⟨PUnit, inferInstance, ⟨splitTorus.gmIso S⟩⟩

/-- Binary products of split tori are split tori. -/
theorem IsSplitTorus.tensor {G H : GroupScheme S} (hG : IsSplitTorus G) (hH : IsSplitTorus H) :
    IsSplitTorus (G ⊗ H) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  obtain ⟨J, hJ, ⟨f⟩⟩ := hH
  exact ⟨I ⊕ J, inferInstance, ⟨(e ⊗ᵢ f) ≪≫ splitTorus.prodIso I J⟩⟩

/-- Split tori are smooth over their base. -/
theorem smooth_splitTorus (I : Type u) [Finite I] : Smooth (splitTorus S I).X.hom :=
  smooth_pi _ fun _ => smooth_gm S

/-- A split torus is smooth over its base. -/
theorem IsSplitTorus.smooth {G : GroupScheme S} (hG : IsSplitTorus G) : Smooth G.X.hom := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact smooth_of_over_iso ((Grp.forget _).mapIso e) (smooth_splitTorus I)

/-! ### Base change -/

namespace splitTorus

variable {S' : Scheme.{u}} (b : S' ⟶ S) (I : Type u) [Finite I]

/-- The point model of the base change of a split torus. -/
def baseChangePointsEquiv (T : Over S') :
    (T ⟶ ((baseChange b).obj (splitTorus S I)).X) ≃* (I → (Γ(T.left, ⊤))ˣ) :=
  (GroupScheme.baseChangePointsEquiv b (splitTorus S I) T).trans
    (pointsEquiv I ((Over.map b).obj T))

theorem baseChangePointsEquiv_naturality {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((baseChange b).obj (splitTorus S I)).X) :
    baseChangePointsEquiv b I T' (a ≫ x) =
      unitsRestrict I a (baseChangePointsEquiv b I T x) := by
  rw [baseChangePointsEquiv, MulEquiv.trans_apply,
    GroupScheme.baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  rfl

/-- Base change of the split torus on `I` along `b : S' ⟶ S` is the split torus on `I`. -/
def baseChangeIso : (baseChange b).obj (splitTorus S I) ≅ splitTorus S' I :=
  isoOfPointModels (fun T : Over S' => I → (Γ(T.left, ⊤))ˣ)
    (fun a => unitsRestrict I a) (baseChangePointsEquiv b I) (pointsEquiv I)
    (fun a x => baseChangePointsEquiv_naturality b I a x)
    (fun a y => pointsEquiv_naturality I a y)

end splitTorus

/-- Split tori stay split after arbitrary base change. -/
theorem IsSplitTorus.baseChange {S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}
    (hG : IsSplitTorus G) : IsSplitTorus ((baseChange b).obj G) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact ⟨I, hI, ⟨(GroupScheme.baseChange b).mapIso e ≪≫ splitTorus.baseChangeIso b I⟩⟩

end Langlands.GroupScheme
