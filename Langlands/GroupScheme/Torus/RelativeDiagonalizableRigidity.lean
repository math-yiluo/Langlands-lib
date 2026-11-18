import Langlands.GroupScheme.Torus.DiagonalizableRigidityProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.AbelianScheme.KernelBaseChange

/-! # Rigidity of families of homomorphisms between diagonalizable groups over a base

Let `S` be a scheme and `X` a scheme over `S` all of whose fibres `X_s` are preconnected. A family
of homomorphisms `D_S(Λ) → D_S(Λ')` parametrized by `X`, given on points over every `S`-scheme
(multiplicative in the group variable and natural in the test scheme), does not depend on the
parameter: two parameters `a a' : V ⟶ X` over the same test scheme give the same homomorphism.

The proof applies the locus decomposition of `DiagonalizableRigidity.CharFamily` to each
coordinate of the family: every locus is open and closed in `X`, so it is a union of fibres, and
two parameters over the same test scheme meet the same loci.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace DiagonalizableRigidity.CharFamily

variable {X : Scheme.{u}} {Λ : Type u} [AddCommGroup Λ] (c : CharFamily X Λ)

/-- The family restricted along a morphism `w : W ⟶ X`. -/
def comp {W : Scheme.{u}} (w : W ⟶ X) : CharFamily W Λ where
  app {_} y := c.app (y ≫ w)
  naturality t y χ := by
    simpa only [Category.assoc] using c.naturality t (y ≫ w) χ

/-- A point of `W` whose image lies in the locus of `m` lies in the locus of `m` of the
restricted family. -/
theorem mem_locus_comp {W : Scheme.{u}} (w : W ⟶ X) {m : Λ} {x : W}
    (h : w x ∈ c.Locus m) : x ∈ (c.comp w).Locus m := by
  intro Y' t χ
  change c.app ((t ≫ W.fromSpecResidueField x) ≫ w) χ = χ (.ofAdd m)
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc]
  exact h Y' _ χ

/-- If a point `y` of `X` takes all its values in the locus of `m`, the family is evaluation at
`m` over `y`. -/
theorem app_eq_of_forall_mem_locus {m : Λ} {Y : Scheme.{u}} (y : Y ⟶ X)
    (h : ∀ z, y z ∈ c.Locus m) (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ) :
    c.app y χ = χ (.ofAdd m) := by
  have := (c.comp y).app_eq_of_locus (fun z => c.mem_locus_comp y (h z)) (𝟙 Y) χ
  change c.app (𝟙 Y ≫ y) χ = _ at this
  rwa [Category.id_comp] at this

/-- Two points `y y'` of `X` over the same test scheme give the same homomorphism if, at every
point `z`, the locus containing `y z` also contains `y' z`. -/
theorem app_eq_app_of_locus {Y : Scheme.{u}} (y y' : Y ⟶ X)
    (h : ∀ (z : Y) (m : Λ), y z ∈ c.Locus m → y' z ∈ c.Locus m)
    (χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ) : c.app y χ = c.app y' χ := by
  let U : Λ → Y.Opens := fun m => y ⁻¹ᵁ ⟨c.Locus m, c.isOpen_locus m⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨m, hm⟩ := c.exists_mem_locus (y z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, hm⟩
  apply Units.ext
  refine eq_of_cover (Y.openCoverOfIsOpenCover U hU) fun m => ?_
  have h1 := c.naturality (U m).ι y χ
  have h2 := c.naturality (U m).ι y' χ
  have e1 := c.app_eq_of_forall_mem_locus ((U m).ι ≫ y) (m := m)
    (fun z => by rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact z.2)
    (resChar (U m).ι χ)
  have e2 := c.app_eq_of_forall_mem_locus ((U m).ι ≫ y') (m := m)
    (fun z => by rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact h _ m z.2)
    (resChar (U m).ι χ)
  have := (h1.symm.trans e1).trans (e2.symm.trans h2)
  exact congrArg Units.val this

end DiagonalizableRigidity.CharFamily

namespace RelativeDiagonalizableRigidity

open DiagonalizableRigidity RelativeMultiplicativeType

variable {S : Scheme.{u}} {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']

/-- The points of `D_S(Λ)` over an `S`-scheme `V` are the characters `Λ → Γ(V, 𝒪_V)ˣ`: the
pullback adjunction to points of `D(Λ)` over `Spec ℤ`, followed by the character description. -/
def pointsEquiv (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] (V : Over S) :
    (V ⟶ (diagonalizable S Λ).X) ≃* (Multiplicative Λ →* Γ(V.left, ⊤)ˣ) :=
  (baseChangePointsEquiv (Gm.toSpecZ S)
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).toGrp V).trans
    (Diagonalizable.characterPointsEquiv (CommRingCat.of (ULift.{u} ℤ)) Λ _)

/-- The character of a restricted point is the restricted character. -/
theorem pointsEquiv_comp {V V' : Over S} (a : V' ⟶ V) (x : V ⟶ (diagonalizable S Λ).X) :
    pointsEquiv S Λ V' (a ≫ x) = resChar a.left (pointsEquiv S Λ V x) := by
  change Diagonalizable.characterPointsEquiv _ Λ _
      (baseChangePointsEquiv (Gm.toSpecZ S) _ V' (a ≫ x)) = _
  rw [baseChangePointsEquiv_naturality]
  exact characterPointsEquiv_comp ((Over.map _).map a) _

section Family

variable {X : Over S}
  (F : ∀ V : Over S, (V ⟶ X) → (V ⟶ (diagonalizable S Λ).X) → (V ⟶ (diagonalizable S Λ').X))
  (hmul : ∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ (diagonalizable S Λ).X),
    F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
  (hnat : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ (diagonalizable S Λ).X),
    F W (f ≫ a) (f ≫ t) = f ≫ F V a t)

/-- The family at the parameter `a`, as a homomorphism of character groups. -/
def charHom {V : Over S} (a : V ⟶ X) :
    (Multiplicative Λ →* Γ(V.left, ⊤)ˣ) →* (Multiplicative Λ' →* Γ(V.left, ⊤)ˣ) :=
  (pointsEquiv S Λ' V).toMonoidHom.comp
    ((MonoidHom.mk' (F V a) (hmul V a)).comp (pointsEquiv S Λ V).symm.toMonoidHom)

theorem charHom_apply {V : Over S} (a : V ⟶ X) (χ : Multiplicative Λ →* Γ(V.left, ⊤)ˣ) :
    charHom F hmul a χ = pointsEquiv S Λ' V (F V a ((pointsEquiv S Λ V).symm χ)) :=
  rfl

include hmul hnat in
/-- The `l`-th coordinate of the family, as a family of characters of `D(Λ)` parametrized by the
scheme `X.left`. A point `y : Y ⟶ X.left` makes `Y` a scheme over `S` through `y ≫ X.hom`. -/
def charFamily (l : Λ') : CharFamily X.left Λ where
  app {Y} y :=
    { toFun := fun χ =>
        charHom F hmul (Over.homMk y : Over.mk (y ≫ X.hom) ⟶ X) χ (.ofAdd l)
      map_one' := by
        rw [map_one]
        rfl
      map_mul' := fun χ χ' => by
        rw [map_mul]
        rfl }
  naturality {Y Y'} t y χ := by
    let a : Over.mk ((t ≫ y) ≫ X.hom) ⟶ Over.mk (y ≫ X.hom) := Over.homMk t (by simp)
    have h1 : (Over.homMk (t ≫ y) : Over.mk ((t ≫ y) ≫ X.hom) ⟶ X) =
        a ≫ Over.homMk y := by
      ext
      simp [a]
    have h2 : (pointsEquiv S Λ (Over.mk ((t ≫ y) ≫ X.hom))).symm (resChar t χ) =
        a ≫ (pointsEquiv S Λ (Over.mk (y ≫ X.hom))).symm χ := by
      apply (pointsEquiv S Λ _).injective
      rw [MulEquiv.apply_symm_apply, pointsEquiv_comp, MulEquiv.apply_symm_apply]
      rfl
    change pointsEquiv S Λ' (Over.mk ((t ≫ y) ≫ X.hom))
        (F _ (Over.homMk (t ≫ y))
          ((pointsEquiv S Λ (Over.mk ((t ≫ y) ≫ X.hom))).symm (resChar t χ))) (.ofAdd l) =
      Units.map t.appTop.hom.toMonoidHom
        (pointsEquiv S Λ' (Over.mk (y ≫ X.hom))
          (F _ (Over.homMk y) ((pointsEquiv S Λ (Over.mk (y ≫ X.hom))).symm χ)) (.ofAdd l))
    rw [h1, h2, hnat, pointsEquiv_comp]
    rfl

/-- The coordinates of `F T x g` are the values of the coordinate families at `x.left`. -/
theorem charFamily_app (l : Λ') {T : Over S} (x : T ⟶ X)
    (g : T ⟶ (diagonalizable S Λ).X) :
    pointsEquiv S Λ' T (F T x g) (.ofAdd l) =
      (charFamily F hmul hnat l).app x.left (pointsEquiv S Λ T g) := by
  let e : T ⟶ Over.mk (x.left ≫ X.hom) := Over.homMk (𝟙 T.left) (by simp [Over.w x])
  have hx : e ≫ (Over.homMk x.left : Over.mk (x.left ≫ X.hom) ⟶ X) = x := by
    ext
    simp [e]
  have hg : e ≫ (pointsEquiv S Λ (Over.mk (x.left ≫ X.hom))).symm
      (pointsEquiv S Λ T g) = g := by
    apply (pointsEquiv S Λ T).injective
    rw [pointsEquiv_comp, MulEquiv.apply_symm_apply]
    ext l
    simp [e]
  have key : F T x g = e ≫ F _ (Over.homMk x.left : Over.mk (x.left ≫ X.hom) ⟶ X)
      ((pointsEquiv S Λ (Over.mk (x.left ≫ X.hom))).symm (pointsEquiv S Λ T g)) := by
    rw [← hnat, hx, hg]
  rw [key, pointsEquiv_comp]
  change Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _ = _
  simp
  rfl

include hmul hnat in
/-- **Rigidity over a base with preconnected fibres** for the split groups `D_S(Λ)`,
`D_S(Λ')`. -/
theorem eq_of_preconnected_fibres (hX : ∀ s : S, _root_.IsPreconnected (X.hom ⁻¹' {s}))
    {V : Over S} (a a' : V ⟶ X) (t : V ⟶ (diagonalizable S Λ).X) :
    F V a t = F V a' t := by
  apply (pointsEquiv S Λ' V).injective
  apply MonoidHom.ext
  intro l
  rw [← ofAdd_toAdd l, charFamily_app F hmul hnat l.toAdd a t,
    charFamily_app F hmul hnat l.toAdd a' t]
  apply CharFamily.app_eq_app_of_locus
  intro z m hm
  have hz : X.hom (a'.left z) = X.hom (a.left z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w a, Over.w a']
  exact (hX (X.hom (a.left z))).subset_isClopen
    ⟨(charFamily F hmul hnat l.toAdd).isClosed_locus m,
      (charFamily F hmul hnat l.toAdd).isOpen_locus m⟩
    ⟨a.left z, rfl, hm⟩ hz

end Family

/-- **Rigidity over a base with preconnected fibres.** Let `X` be a scheme over `S` with
preconnected fibres and `D`, `D'` diagonalizable `S`-groups. A family of homomorphisms
`D → D'` parametrized by `X`, multiplicative and natural on points, takes the same value at any
two parameters over the same test scheme. -/
theorem eq_of_isDiagonalizable {X : Over S}
    (hX : ∀ s : S, _root_.IsPreconnected (X.hom ⁻¹' {s}))
    {D D' : GroupScheme S} (hD : IsDiagonalizable D) (hD' : IsDiagonalizable D')
    (F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X))
    (hmul : ∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ D.X),
      F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
    (hnat : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ D.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t)
    {V : Over S} (a a' : V ⟶ X) (t : V ⟶ D.X) : F V a t = F V a' t := by
  obtain ⟨Λ, _, _, ⟨eD⟩⟩ := hD
  obtain ⟨Λ', _, _, ⟨eD'⟩⟩ := hD'
  let F' : ∀ V : Over S, (V ⟶ X) → (V ⟶ (diagonalizable S Λ).X) →
      (V ⟶ (diagonalizable S Λ').X) :=
    fun V a t => F V a (t ≫ eD.inv.hom.hom) ≫ eD'.hom.hom.hom
  have hmul' : ∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ (diagonalizable S Λ).X),
      F' V a (t₁ * t₂) = F' V a t₁ * F' V a t₂ := by
    intro V a t₁ t₂
    simp only [F', MonObj.mul_comp, hmul]
  have hnat' : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ (diagonalizable S Λ).X),
      F' W (f ≫ a) (f ≫ t) = f ≫ F' V a t := by
    intro V W f a t
    simp only [F', Category.assoc, hnat]
  have h : ∀ b : V ⟶ X, F' V b (t ≫ eD.hom.hom.hom) = F V b t ≫ eD'.hom.hom.hom := by
    intro b
    simp only [F', Category.assoc]
    rw [← Grp.comp_hom_hom, eD.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have key := eq_of_preconnected_fibres F' hmul' hnat' hX a a' (t ≫ eD.hom.hom.hom)
  rw [h, h] at key
  exact (cancel_mono eD'.hom.hom.hom).mp key

end RelativeDiagonalizableRigidity

end Langlands.GroupScheme
