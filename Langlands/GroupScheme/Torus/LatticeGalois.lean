import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.CocharacterTransport
import Mathlib.RepresentationTheory.Basic

/-! # Galois transport of character and cocharacter lattices

For a commutative group scheme `T` over `B`, a morphism `b : S ⟶ B` and an endomorphism
`a : S ⟶ S` over `B`, characters and cocharacters of the base change `T_S` are transported along
`a` by base change and the canonical descent identification. For a field extension `K / k` and
`σ ∈ Aut_k(K)`, transport along `Spec σ` is the natural action `(σ χ)(t) = σ (χ (σ⁻¹ t))` of the
automorphism group on `X^*(T_K)` and `X_*(T_K)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Transport of points and characters -/

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)

/-- A point of the pulled-back group over `T`, seen over the same scheme `T` with its
`S`-structure changed by `a`: both are the same point of `G` over `B`. -/
def descentPoint (T : Over S) (y : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    (Over.map a).obj T ⟶ ((Over.pullback b).mapGrp.obj G).X :=
  (baseChangePointsEquiv b G ((Over.map a).obj T)).symm
    ((descentTestIso b a ha T).inv ≫ baseChangePointsEquiv b G T y)

theorem baseChangePointsEquiv_descentPoint (T : Over S)
    (y : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    baseChangePointsEquiv b G ((Over.map a).obj T) (descentPoint b a ha G T y) =
      (descentTestIso b a ha T).inv ≫ baseChangePointsEquiv b G T y :=
  MulEquiv.apply_symm_apply _ _

theorem descentPoint_mul (T : Over S) (y z : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    descentPoint b a ha G T (y * z) = descentPoint b a ha G T y * descentPoint b a ha G T z := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [map_mul, baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_descentPoint,
    baseChangePointsEquiv_descentPoint, map_mul, MonObj.comp_mul]

theorem descentPoint_injective (T : Over S) : Function.Injective (descentPoint b a ha G T) := by
  intro y z h
  apply (baseChangePointsEquiv b G T).injective
  have h' := congrArg (baseChangePointsEquiv b G ((Over.map a).obj T)) h
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_descentPoint] at h'
  exact (cancel_epi _).1 h'

/-- Transport of a character of a group pulled back from `B` along a base endomorphism over `B`:
base change along `a`, followed by the descent identification and the base change of `𝔾_m`. -/
def transportCharacter (χ : (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp) :
    (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp :=
  (descentBaseChangeIso b a ha G).inv ≫ (Over.pullback a).mapGrp.map χ ≫ (Gm.baseChangeIso a).hom

/-- The transported character evaluates the original character at the same point of `G`, seen
with the changed `S`-structure. -/
theorem transportCharacter_points (χ : (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp)
    (T : Over S) (y : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    Gm.pointsEquiv S T (y ≫ (transportCharacter b a ha G χ).hom.hom) =
      Gm.pointsEquiv S ((Over.map a).obj T) (descentPoint b a ha G T y ≫ χ.hom.hom) := by
  set y' := y ≫ (descentBaseChangeIso b a ha G).inv.hom.hom with hy'
  have h1 : (descentBaseChangeIso b a ha G).inv.hom.hom ≫
      (descentBaseChangeIso b a ha G).hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (descentBaseChangeIso b a ha G).inv_hom_id
  have hy : y = y' ≫ (descentBaseChangeIso b a ha G).hom.hom.hom := by
    rw [hy', Category.assoc, h1, Category.comp_id]
  have key := baseChangePointsEquiv_descent b a ha G T y'
  rw [← hy] at key
  change Gm.pointsEquiv S T ((y' ≫ ((Over.pullback a).mapGrp.map χ).hom.hom) ≫
      (Gm.baseChangeIso a).hom.hom.hom) = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    baseChangePointsEquiv_comp]
  congr 2
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, key, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The transported cocharacter, seen through `descentPoint`, is the original cocharacter at the
same unit. -/
theorem descentPoint_transportCocharacter (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G)
    (T : Over S) (x : T ⟶ (Gm S).X) :
    descentPoint b a ha G T (x ≫ (transportCocharacter b a ha G χ).hom.hom) =
      (Gm.pointsEquiv S ((Over.map a).obj T)).symm (Gm.pointsEquiv S T x) ≫ χ.hom.hom := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, transportCocharacter_points, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Changing the `S`-structure along `𝟙 S` does not change a point. -/
theorem descentPoint_id (T : Over S) (y : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    descentPoint b (𝟙 S) (Category.id_comp b) G T y =
      (Over.isoMk (Iso.refl T.left) (by simp) : (Over.map (𝟙 S)).obj T ≅ T).hom ≫ y := by
  apply (baseChangePointsEquiv b G ((Over.map (𝟙 S)).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_naturality]
  congr 1

/-- Two successive changes of the `S`-structure are one change along the composite. -/
theorem descentPoint_comp (c : S ⟶ S) (hc : c ≫ b = b) (T : Over S)
    (y : T ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    (Over.isoMk (Iso.refl T.left) (by simp) :
        (Over.map (a ≫ c)).obj T ≅ (Over.map c).obj ((Over.map a).obj T)).hom ≫
      descentPoint b c hc G ((Over.map a).obj T) (descentPoint b a ha G T y) =
    descentPoint b (a ≫ c) (by rw [Category.assoc, hc, ha]) G T y := by
  apply (baseChangePointsEquiv b G ((Over.map (a ≫ c)).obj T)).injective
  rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_descentPoint,
    baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_descentPoint]
  apply Over.OverMorphism.ext
  rfl

/-- Transport along the identity is the identity. -/
theorem transportCharacter_id (χ : (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp) :
    transportCharacter b (𝟙 S) (Category.id_comp b) G χ = χ := by
  apply hom_ext_points
  intro T y
  apply (Gm.pointsEquiv S T).injective
  rw [transportCharacter_points, descentPoint_id, Category.assoc, Gm.pointsEquiv_naturality]
  change Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _ = _
  simp

/-- Successive transports compose in the geometric order of the base maps. -/
theorem transportCharacter_comp (c : S ⟶ S) (hc : c ≫ b = b)
    (χ : (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp) :
    transportCharacter b a ha G (transportCharacter b c hc G χ) =
      transportCharacter b (a ≫ c) (by rw [Category.assoc, hc, ha]) G χ := by
  apply hom_ext_points
  intro T y
  apply (Gm.pointsEquiv S T).injective
  rw [transportCharacter_points, transportCharacter_points, transportCharacter_points]
  conv_rhs => rw [← descentPoint_comp b a ha G c hc, Category.assoc, Gm.pointsEquiv_naturality]
  change _ = Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _
  simp

end Transport

/-! ### Transport on the lattices of a commutative group scheme -/

section LatticeTransport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (T : CommGroupScheme B)

namespace characterLattice

/-- Transport of characters of the base change `T_S` along an endomorphism `a` of `S` over `B`,
as an additive map of character lattices. -/
def transport : characterLattice ((CommGroupScheme.baseChange b).obj T) →+
    characterLattice ((CommGroupScheme.baseChange b).obj T) :=
  AddMonoidHom.mk'
    (fun χ => Additive.ofMul (transportCharacter b a ha T.toGrp (CommGroupScheme.groupHom χ)))
    (fun χ ψ => by
      apply CommGroupScheme.hom_ext_points
      intro U y
      rw [comp_groupHom_add]
      apply (Gm.pointsEquiv S U).injective
      rw [map_mul]
      refine (transportCharacter_points b a ha T.toGrp _ U y).trans ?_
      refine Eq.trans ?_ (congrArg₂ (· * ·) (transportCharacter_points b a ha T.toGrp _ U y).symm
        (transportCharacter_points b a ha T.toGrp _ U y).symm)
      exact (congrArg (Gm.pointsEquiv S ((Over.map a).obj U))
        (comp_groupHom_add (G := (CommGroupScheme.baseChange b).obj T) (H := Gm S) _ χ ψ)).trans
        (map_mul _ _ _))

theorem groupHom_transport (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    CommGroupScheme.groupHom (transport b a ha T χ) =
      transportCharacter b a ha T.toGrp (CommGroupScheme.groupHom χ) := rfl

/-- On points, the transported character evaluates the original one at the same point of `T`,
seen with the `S`-structure changed by `a`. -/
theorem transport_points (χ : characterLattice ((CommGroupScheme.baseChange b).obj T))
    (U : Over S) (y : U ⟶ ((CommGroupScheme.baseChange b).obj T).X) :
    Gm.pointsEquiv S U (y ≫ (CommGroupScheme.groupHom (transport b a ha T χ)).hom.hom) =
      Gm.pointsEquiv S ((Over.map a).obj U)
        (descentPoint b a ha T.toGrp U y ≫ (CommGroupScheme.groupHom χ).hom.hom) :=
  transportCharacter_points b a ha T.toGrp _ U y

theorem transport_id (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b (𝟙 S) (Category.id_comp b) T χ = χ :=
  congrArg Additive.ofMul (transportCharacter_id b T.toGrp _)

theorem transport_transport (c : S ⟶ S) (hc : c ≫ b = b)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T (transport b c hc T χ) =
      transport b (a ≫ c) (by rw [Category.assoc, hc, ha]) T χ :=
  congrArg Additive.ofMul (transportCharacter_comp b a ha T.toGrp c hc _)

theorem transport_of_eq_id (h : a = 𝟙 S)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T χ = χ := by
  subst h
  exact transport_id b T χ

theorem transport_transport_of_eq (c : S ⟶ S) (hc : c ≫ b = b) (d : S ⟶ S) (hd : d ≫ b = b)
    (h : a ≫ c = d) (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T (transport b c hc T χ) = transport b d hd T χ := by
  subst h
  exact transport_transport b a ha T c hc χ

end characterLattice

namespace cocharacterLattice

/-- Transport of cocharacters of the base change `T_S` along an endomorphism `a` of `S` over
`B`, as an additive map of cocharacter lattices. -/
def transport : cocharacterLattice ((CommGroupScheme.baseChange b).obj T) →+
    cocharacterLattice ((CommGroupScheme.baseChange b).obj T) :=
  AddMonoidHom.mk'
    (fun ν => Additive.ofMul (transportCocharacter b a ha T.toGrp (CommGroupScheme.groupHom ν)))
    (fun ν ν' => by
      apply CommGroupScheme.hom_ext_points
      intro U x
      rw [comp_groupHom_add]
      apply descentPoint_injective b a ha T.toGrp U
      rw [descentPoint_mul]
      refine (descentPoint_transportCocharacter b a ha T.toGrp _ U x).trans ?_
      refine Eq.trans ?_ (congrArg₂ (· * ·)
        (descentPoint_transportCocharacter b a ha T.toGrp _ U x).symm
        (descentPoint_transportCocharacter b a ha T.toGrp _ U x).symm)
      exact comp_groupHom_add (G := Gm S) (H := (CommGroupScheme.baseChange b).obj T) _ ν ν')

theorem groupHom_transport (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    CommGroupScheme.groupHom (transport b a ha T ν) =
      transportCocharacter b a ha T.toGrp (CommGroupScheme.groupHom ν) := rfl

/-- On points, the transported cocharacter, seen through `descentPoint`, is the original one at
the same unit. -/
theorem descentPoint_transport (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T))
    (U : Over S) (x : U ⟶ (Gm S).X) :
    descentPoint b a ha T.toGrp U (x ≫ (CommGroupScheme.groupHom (transport b a ha T ν)).hom.hom) =
      (Gm.pointsEquiv S ((Over.map a).obj U)).symm (Gm.pointsEquiv S U x) ≫
        (CommGroupScheme.groupHom ν).hom.hom :=
  descentPoint_transportCocharacter b a ha T.toGrp _ U x

theorem transport_id (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b (𝟙 S) (Category.id_comp b) T ν = ν :=
  congrArg Additive.ofMul (transportCocharacter_id b T.toGrp _)

theorem transport_transport (c : S ⟶ S) (hc : c ≫ b = b)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T (transport b c hc T ν) =
      transport b (a ≫ c) (by rw [Category.assoc, hc, ha]) T ν :=
  congrArg Additive.ofMul (transportCocharacter_comp b a ha T.toGrp c hc _)

theorem transport_of_eq_id (h : a = 𝟙 S)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T ν = ν := by
  subst h
  exact transport_id b T ν

theorem transport_transport_of_eq (c : S ⟶ S) (hc : c ≫ b = b) (d : S ⟶ S) (hd : d ≫ b = b)
    (h : a ≫ c = d) (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    transport b a ha T (transport b c hc T ν) = transport b d hd T ν := by
  subst h
  exact transport_transport b a ha T c hc ν

end cocharacterLattice

end LatticeTransport

/-! ### Two readings of the points of a base change -/

/-- A composite into the base change of a commutative group scheme, read with codomain the base
change as a commutative group scheme or as a group scheme. The two readings are the same
morphism; rewriting with this lemma only changes the implicit codomain of `≫`, which keeps
kernel checking of concrete instances cheap. -/
theorem comp_baseChange_X {B S : Scheme.{u}} (b : S ⟶ B) (T : CommGroupScheme B) {U V : Over S}
    (x : U ⟶ V) (f : V ⟶ ((CommGroupScheme.baseChange b).obj T).X) :
    (x ≫ f : U ⟶ ((CommGroupScheme.baseChange b).obj T).X) =
      (x ≫ f : U ⟶ ((Over.pullback b).mapGrp.obj T.toGrp).X) := rfl

/-- A composite with a homomorphism of commutative group schemes, read with codomain the target
as a commutative group scheme, or with the codomain of the underlying monoid morphism. -/
theorem comp_groupHom_X {S : Scheme.{u}} {G T : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X)
    (g : G ⟶ T) :
    (x ≫ (CommGroupScheme.groupHom g).hom.hom : U ⟶ T.X) =
      x ≫ (CommGroupScheme.groupHom g).hom.hom := rfl

/-! ### Extensionality on points -/

section Ext

variable {S : Scheme.{u}} {T : CommGroupScheme S}

/-- Two characters agreeing on all points, read in `𝔾_m` through its units model, are equal. -/
theorem characterLattice.ext_points {χ ψ : characterLattice T}
    (h : ∀ (U : Over S) (y : U ⟶ T.X),
      Gm.pointsEquiv S U (y ≫ (CommGroupScheme.groupHom χ).hom.hom) =
        Gm.pointsEquiv S U (y ≫ (CommGroupScheme.groupHom ψ).hom.hom)) : χ = ψ :=
  CommGroupScheme.hom_ext_points fun U y => (Gm.pointsEquiv S U).injective (h U y)

/-- Two cocharacters agreeing on all points are equal. -/
theorem cocharacterLattice.ext_points {ν ν' : cocharacterLattice T}
    (h : ∀ (U : Over S) (x : U ⟶ (Gm S).X),
      (x ≫ (CommGroupScheme.groupHom ν).hom.hom : U ⟶ T.X) =
        (x ≫ (CommGroupScheme.groupHom ν').hom.hom : U ⟶ T.X)) : ν = ν' :=
  CommGroupScheme.hom_ext_points h

end Ext

/-! ### Lattices along isomorphisms -/

section Congr

variable {S : Scheme.{u}} {T T' : CommGroupScheme S} (e : T ≅ T')

/-- An isomorphism of commutative group schemes identifies the character lattices, by
precomposition with its inverse. -/
def characterLattice.congr : characterLattice T ≃+ characterLattice T' where
  toFun χ := e.inv ≫ χ
  invFun ψ := e.hom ≫ ψ
  left_inv χ := by simp
  right_inv ψ := by simp
  map_add' χ ψ := Preadditive.comp_add _ _ _ _ _ _

theorem characterLattice.congr_apply (χ : characterLattice T) :
    characterLattice.congr e χ = e.inv ≫ χ := rfl

theorem characterLattice.congr_symm_apply (ψ : characterLattice T') :
    (characterLattice.congr e).symm ψ = e.hom ≫ ψ := rfl

/-- An isomorphism of commutative group schemes identifies the cocharacter lattices, by
composition with it. -/
def cocharacterLattice.congr : cocharacterLattice T ≃+ cocharacterLattice T' where
  toFun ν := ν ≫ e.hom
  invFun ν := ν ≫ e.inv
  left_inv ν := by simp
  right_inv ν := by simp
  map_add' ν ν' := Preadditive.add_comp _ _ _ _ _ _

theorem cocharacterLattice.congr_apply (ν : cocharacterLattice T) :
    cocharacterLattice.congr e ν = ν ≫ e.hom := rfl

theorem cocharacterLattice.congr_symm_apply (ν : cocharacterLattice T') :
    (cocharacterLattice.congr e).symm ν = ν ≫ e.inv := rfl

/-- The identifications of lattices along an isomorphism preserve the pairing. -/
theorem latticePairing_congr {k : Type u} [CommRing k] [IsDomain k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))} (e : T ≅ T') (χ : characterLattice T)
    (ν : cocharacterLattice T) :
    latticePairing T' (characterLattice.congr e χ) (cocharacterLattice.congr e ν) =
      latticePairing T χ ν := by
  rw [latticePairing_apply, latticePairing_apply, characterLattice.congr_apply,
    cocharacterLattice.congr_apply, Category.assoc, Iso.hom_inv_id_assoc]

end Congr

/-! ### Galois action -/

section Galois

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

/-- The base morphism `Spec K ⟶ Spec k` of a `k`-algebra `K`, for instance of a field
extension. -/
abbrev algebraBaseMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The automorphism `Spec σ` of `Spec K` attached to `σ ∈ Aut_k(K)`. -/
def galoisBaseMap (σ : K ≃ₐ[k] K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

/-- `Spec σ` is a morphism over `Spec k`. -/
theorem galoisBaseMap_over (σ : K ≃ₐ[k] K) :
    galoisBaseMap k K σ ≫ algebraBaseMap k K = algebraBaseMap k K := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k K)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact σ.toAlgHom.comp_algebraMap

@[simp] theorem galoisBaseMap_one : galoisBaseMap k K (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  change Spec.map (𝟙 (CommRingCat.of K)) = _
  exact Spec.map_id _

/-- `Spec` reverses composition, so `Spec (σ τ) = Spec σ ≫ Spec τ` in diagrammatic order. -/
theorem galoisBaseMap_mul (σ τ : K ≃ₐ[k] K) :
    galoisBaseMap k K (σ * τ) = galoisBaseMap k K σ ≫ galoisBaseMap k K τ := by
  unfold galoisBaseMap
  rw [← Spec.map_comp]
  rfl

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

namespace characterLattice

/-- The Galois action of `Aut_k(K)` on the character lattice `X^*(T_K)`: `σ` acts by transport
along `Spec σ`, which on points is `(σ χ)(t) = σ (χ (σ⁻¹ t))`. -/
def galoisRepresentation : Representation ℤ (K ≃ₐ[k] K)
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) where
  toFun σ := (transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
    T).toIntLinearMap
  map_one' := LinearMap.ext fun χ =>
    transport_of_eq_id (algebraBaseMap k K) _ _ T (galoisBaseMap_one k K) χ
  map_mul' σ τ := LinearMap.ext fun χ =>
    (transport_transport_of_eq (algebraBaseMap k K) _ _ T _ _ _ _
      (galoisBaseMap_mul k K σ τ).symm χ).symm

theorem galoisRepresentation_apply (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    galoisRepresentation k K T σ χ =
      transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T χ := rfl

/-- On points, `σ χ` evaluates `χ` at the same point of `T`, seen with the `K`-structure changed
by `Spec σ`. -/
theorem galoisRepresentation_points (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (U : Over (Spec (CommRingCat.of K)))
    (y : U ⟶ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).X) :
    Gm.pointsEquiv _ U (y ≫ (CommGroupScheme.groupHom (galoisRepresentation k K T σ χ)).hom.hom) =
      Gm.pointsEquiv _ ((Over.map (galoisBaseMap k K σ)).obj U)
        (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
          T.toGrp U y ≫ (CommGroupScheme.groupHom χ).hom.hom) := by
  rw [galoisRepresentation_apply]
  exact transport_points (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T
    χ U y

end characterLattice

namespace cocharacterLattice

/-- The Galois action of `Aut_k(K)` on the cocharacter lattice `X_*(T_K)`: `σ` acts by transport
along `Spec σ`, which on points is `(σ ν)(s) = σ (ν (σ⁻¹ s))`. -/
def galoisRepresentation : Representation ℤ (K ≃ₐ[k] K)
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) where
  toFun σ := (transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
    T).toIntLinearMap
  map_one' := LinearMap.ext fun ν =>
    transport_of_eq_id (algebraBaseMap k K) _ _ T (galoisBaseMap_one k K) ν
  map_mul' σ τ := LinearMap.ext fun ν =>
    (transport_transport_of_eq (algebraBaseMap k K) _ _ T _ _ _ _
      (galoisBaseMap_mul k K σ τ).symm ν).symm

theorem galoisRepresentation_apply (σ : K ≃ₐ[k] K)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    galoisRepresentation k K T σ ν =
      transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T ν := rfl

/-- On points, `σ ν`, seen through the change of `K`-structure by `Spec σ`, is `ν` at the same
unit. -/
theorem descentPoint_galoisRepresentation (σ : K ≃ₐ[k] K)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (U : Over (Spec (CommRingCat.of K))) (x : U ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T.toGrp U
        (x ≫ (CommGroupScheme.groupHom (galoisRepresentation k K T σ ν)).hom.hom :
          U ⟶ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).X) =
      ((Gm.pointsEquiv _ ((Over.map (galoisBaseMap k K σ)).obj U)).symm (Gm.pointsEquiv _ U x) ≫
        (CommGroupScheme.groupHom ν).hom.hom :
          (Over.map (galoisBaseMap k K σ)).obj U ⟶
            ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).X) := by
  rw [galoisRepresentation_apply,
    comp_groupHom_X ((Gm.pointsEquiv _ ((Over.map (galoisBaseMap k K σ)).obj U)).symm
      (Gm.pointsEquiv _ U x)) ν,
    comp_baseChange_X (algebraBaseMap k K) T x]
  exact descentPoint_transport (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) T ν U x

end cocharacterLattice

end Galois

end Langlands.GroupScheme
