import Langlands.GroupScheme.EvenOrthogonalForm.GaloisStage
import Langlands.GroupScheme.EvenOrthogonalForm.Similitude
import Langlands.GroupScheme.OrthogonalMatrix.SpecialOrthogonalAutomorphismStatement
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart

/-! # The similitude cocycle of a form of the split even special orthogonal group

Let `φ` be local isomorphisms from a group scheme `H` over `K` to the split `SO_{2n}` over
`K` along `Spec N ⟶ Spec K`, for a finite Galois extension `N / K`. For each Galois
automorphism `σ`, comparing `φ` at a point `s` and at `s ≫ σ*` gives automorphisms
`ψ_σ` of the split `SO_{2n}` along `Spec N`. Assuming every automorphism of the split
`SO_{2n}` is conjugation by a similitude, `ψ_σ` is conjugation by a similitude `g_σ`, and
the matrices `g_σ` form a cocycle up to scalars, so that `x ↦ g_σ⁻¹ σ(x) g_σ` is an action of
the Galois group on the matrix algebra.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace LocalGroupIso

section Recovery

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A natural local isomorphism is evaluated through its base-change isomorphism: lift the
point to the pullback, apply the isomorphism, and project back. -/
theorem toFun_eq_coverPointsEquiv (e : LocalGroupIso G H U) {T : Over S} (a : T ⟶ U)
    (g : T ⟶ G.X) :
    e.toFun a g = coverPointsEquiv H a
      ((coverPointsEquiv G a).symm g ≫ e.toBaseChangeIso.hom.hom.hom) := by
  conv_lhs => rw [← ofBaseChangeIso_toBaseChangeIso e]
  rfl

end Recovery

section IdentityComponent

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The base-change isomorphism between identity components induced by local isomorphisms
along `Spec N ⟶ Spec K`. -/
def identityComponentBaseChangeIso (e : LocalGroupIso G H (ringTest K N)) :
    (GroupScheme.baseChange (IdentityComponent.specMap (algebraMap K N))).obj
        (identityComponent G) ≅
      (GroupScheme.baseChange (IdentityComponent.specMap (algebraMap K N))).obj
        (identityComponent H) :=
  IdentityComponent.baseChangeIso G (algebraMap K N) ≪≫
    IdentityComponent.mapIso (H := (GroupScheme.baseChange
        (IdentityComponent.specMap (algebraMap K N))).obj G)
      (H' := (GroupScheme.baseChange (IdentityComponent.specMap (algebraMap K N))).obj H)
      e.toBaseChangeIso ≪≫
    (IdentityComponent.baseChangeIso H (algebraMap K N)).symm

theorem identityComponentBaseChangeIso_hom_comp (e : LocalGroupIso G H (ringTest K N)) :
    (identityComponentBaseChangeIso e).hom ≫
        (GroupScheme.baseChange (IdentityComponent.specMap (algebraMap K N))).map
          (identityComponentι H) =
      (GroupScheme.baseChange (IdentityComponent.specMap (algebraMap K N))).map
          (identityComponentι G) ≫ e.toBaseChangeIso.hom := by
  simp only [identityComponentBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [IdentityComponent.baseChangeIso_inv_comp, IdentityComponent.mapIso_hom_identityComponentι,
    IdentityComponent.baseChangeIso_hom_identityComponentι_assoc]

/-- The restriction of local isomorphisms along `Spec N ⟶ Spec K` to identity components. -/
def restrictIdentityComponent (e : LocalGroupIso G H (ringTest K N)) :
    LocalGroupIso (identityComponent G) (identityComponent H) (ringTest K N) :=
  ofBaseChangeIso (U := ringTest K N) (identityComponentBaseChangeIso e)

/-- The restriction to identity components is compatible with the inclusions. -/
theorem restrictIdentityComponent_toFun_comp (e : LocalGroupIso G H (ringTest K N))
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
    (x : V ⟶ (identityComponent G).X) :
    (restrictIdentityComponent e).toFun s x ≫ (identityComponentι H).hom.hom =
      e.toFun s (x ≫ (identityComponentι G).hom.hom) := by
  rw [toFun_eq_coverPointsEquiv e]
  change coverPointsEquiv (identityComponent H) s
      ((coverPointsEquiv (identityComponent G) s).symm x ≫
        (identityComponentBaseChangeIso e).hom.hom.hom) ≫ (identityComponentι H).hom.hom = _
  rw [← coverPointsEquiv_comp]
  have hx : (coverPointsEquiv G s).symm (x ≫ (identityComponentι G).hom.hom) =
      (coverPointsEquiv (identityComponent G) s).symm x ≫
        ((GroupScheme.baseChange (ringTest K N).hom).map (identityComponentι G)).hom.hom := by
    apply (coverPointsEquiv G s).injective
    rw [MulEquiv.apply_symm_apply, coverPointsEquiv_comp, MulEquiv.apply_symm_apply]
  rw [hx, Category.assoc, Category.assoc]
  congr 2
  have h := congrArg (fun f => f.hom.hom) (identityComponentBaseChangeIso_hom_comp e)
  simp only [Grp.comp_hom_hom] at h
  exact h

end IdentityComponent

end LocalGroupIso

namespace EvenOrthogonalForm

open OrthogonalMatrix
open SpecialLinearInnerForm (pointScalars pointScalars_comp_ringTestMap)

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}

section Matrices

/-- The orthogonal matrix of a point of the split `SO_{2n}` over `K`. -/
def splitMatrix {V : Over (Spec (CommRingCat.of K))} (x : V ⟶ (splitGroup K n).X) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤) :=
  pointsEquiv (Fin n) (CommRingCat.of K) V
    (x ≫ (identityComponentι (groupScheme (Fin n) (CommRingCat.of K))).hom.hom)

theorem splitMatrix_injective {V : Over (Spec (CommRingCat.of K))} :
    Function.Injective (splitMatrix (K := K) (n := n) (V := V)) := by
  intro x y h
  have h' := (pointsEquiv (Fin n) (CommRingCat.of K) V).injective (Subtype.ext h)
  have hm : Mono (identityComponentι (groupScheme (Fin n) (CommRingCat.of K))).hom.hom :=
    inferInstance
  exact hm.right_cancellation _ _ h'

/-- Matrices of points of the base change of the split `SO_{2n}` along `Spec N ⟶ Spec K`,
read through the comparison with the split `SO_{2n}` over `N`, are the matrices of the
projected points. -/
theorem splitMatrix_coverPointsEquiv {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N)
    (z : LocalGroupIso.coverTest s ⟶
      ((GroupScheme.baseChange (ringTest K N).hom).obj (splitGroup K n)).X) :
    (↑(pointsEquiv (Fin n) (CommRingCat.of N) (LocalGroupIso.coverTest s)
        (z ≫ (splitBaseChangeIso K N n).hom.hom.hom ≫
          (identityComponentι (groupScheme (Fin n) (CommRingCat.of N))).hom.hom)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ((LocalGroupIso.coverTest s).left, ⊤)) =
      splitMatrix (LocalGroupIso.coverPointsEquiv (splitGroup K n) s z) := by
  have hc : (splitBaseChangeIso K N n).hom ≫
      identityComponentι (groupScheme (Fin n) (CommRingCat.of N)) =
      (GroupScheme.baseChange (ringTest K N).hom).map
          (identityComponentι (groupScheme (Fin n) (CommRingCat.of K))) ≫
        (baseChangeModelIso (Fin n) (algebraBaseMap K N)).hom := by
    simp only [splitBaseChangeIso, Iso.trans_hom, Category.assoc]
    rw [IdentityComponent.mapIso_hom_identityComponentι,
      IdentityComponent.baseChangeIso_hom_identityComponentι_assoc]
    rfl
  have hc' := congrArg (fun f => f.hom.hom) hc
  simp only [Grp.comp_hom_hom] at hc'
  rw [hc', ← Category.assoc]
  have hb := pointsEquiv_baseChangeModelIso_hom (Fin n) (algebraBaseMap K N)
    (T := LocalGroupIso.coverTest s) (z ≫ ((GroupScheme.baseChange (ringTest K N).hom).map
      (identityComponentι (groupScheme (Fin n) (CommRingCat.of K)))).hom.hom)
  have hr : LocalGroupIso.coverPointsEquiv (splitGroup K n) s z ≫
      (identityComponentι (groupScheme (Fin n) (CommRingCat.of K))).hom.hom =
      (LocalGroupIso.coverTestIso s).inv ≫
        GroupScheme.baseChangePointsEquiv (ringTest K N).hom
          (groupScheme (Fin n) (CommRingCat.of K)) (LocalGroupIso.coverTest s)
          (z ≫ ((GroupScheme.baseChange (ringTest K N).hom).map
            (identityComponentι (groupScheme (Fin n) (CommRingCat.of K)))).hom.hom) := by
    rw [← LocalGroupIso.coverPointsEquiv_comp]
    rfl
  have hid : ((LocalGroupIso.coverTestIso s).inv.left.appTop).hom =
      RingHom.id Γ(V.left, ⊤) := by
    change (Scheme.Hom.appTop (𝟙 V.left)).hom = _
    rw [Scheme.Hom.id_appTop]
    rfl
  refine (congrArg Subtype.val hb).trans ?_
  rw [splitMatrix, hr, pointsEquiv_naturality (LocalGroupIso.coverTestIso s).inv, hid, coe_map]
  ext i j
  rfl

end Matrices

section Conjugation

/-- The scalar map `N → Γ(V)` of a point `V ⟶ Spec N` over `Spec K`, valued in the global
sections of `V`. -/
abbrev sectionScalars {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) :
    N →+* Γ(V.left, ⊤) :=
  pointScalars s

/-- Every automorphism of the split `SO_{2n}` along `Spec N ⟶ Spec K` is conjugation by a
similitude, given the automorphism theorem for the split `SO_{2n}` over `N`. -/
theorem exists_similitude_conj (hS : SpecialOrthogonalAutomorphismStatement.{u}) (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    ∃ (g : GL (Fin n ⊕ Fin n) N) (ν : Nˣ),
      IsAlt ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * formMatrix (Fin n) N *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)ᵀ - (ν : N) • formMatrix (Fin n) N) ∧
      ∀ {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
        (x : V ⟶ (splitGroup K n).X),
        splitMatrix (χ.toFun s x) =
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map
            (sectionScalars s) * splitMatrix x *
            (↑g⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map
              (sectionScalars s) := by
  let c := splitBaseChangeIso K N n
  let α : splitGroup N n ≅ splitGroup N n := c.symm ≪≫ χ.toBaseChangeIso ≪≫ c
  obtain ⟨g, ν, hg, hpts⟩ := hS N n hn α
  refine ⟨g, ν, hg, fun {V} s x => ?_⟩
  set y := (LocalGroupIso.coverPointsEquiv (splitGroup K n) s).symm x with hy
  have hα : c.hom.hom.hom ≫ α.hom.hom.hom = χ.toBaseChangeIso.hom.hom.hom ≫ c.hom.hom.hom := by
    have h : c.hom ≫ α.hom = χ.toBaseChangeIso.hom ≫ c.hom := by
      simp only [α, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    have h' := congrArg (fun f => f.hom.hom) h
    simpa only [Grp.comp_hom_hom] using h'
  have hl : (y ≫ χ.toBaseChangeIso.hom.hom.hom) ≫ (splitBaseChangeIso K N n).hom.hom.hom ≫
        (identityComponentι (groupScheme (Fin n) (CommRingCat.of N))).hom.hom =
      (y ≫ c.hom.hom.hom) ≫ α.hom.hom.hom ≫
        (identityComponentι (groupScheme (Fin n) (CommRingCat.of N))).hom.hom := by
    simp only [Category.assoc]
    congr 1
    exact ((reassoc_of% hα) _).symm
  have h1 := hpts (LocalGroupIso.coverTest s) (y ≫ c.hom.hom.hom)
  have h2 := splitMatrix_coverPointsEquiv s y
  have h3 : LocalGroupIso.coverPointsEquiv (splitGroup K n) s y = x := by
    rw [hy]
    exact MulEquiv.apply_symm_apply _ _
  rw [h3] at h2
  have h4 : ((pointsEquiv (Fin n) (CommRingCat.of N) (LocalGroupIso.coverTest s)
      ((y ≫ c.hom.hom.hom) ≫
        (identityComponentι (groupScheme (Fin n) (CommRingCat.of N))).hom.hom) :
          orthogonalGroup (Fin n) Γ((LocalGroupIso.coverTest s).left, ⊤)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ((LocalGroupIso.coverTest s).left, ⊤)) =
      splitMatrix x := by
    rw [Category.assoc]
    exact h2
  rw [LocalGroupIso.toFun_eq_coverPointsEquiv χ, ← splitMatrix_coverPointsEquiv, hl]
  refine h1.trans ?_
  rw [h4]
  rfl

end Conjugation

section Twist

variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))

/-- The automorphisms `ψ_σ(s) = φ(s ≫ σ*) ∘ φ(s)⁻¹` of the split `SO_{2n}` along
`Spec N ⟶ Spec K` obtained by comparing `φ` at a point and at its Galois translate. -/
def galoisTwist (σ : N ≃ₐ[K] N) :
    LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N) where
  toFun s := (φ.toFun s).symm.trans (φ.toFun (s ≫ ringTestMap K σ.toAlgHom))
  naturality t s g := by
    change φ.toFun ((t ≫ s) ≫ ringTestMap K σ.toAlgHom) ((φ.toFun (t ≫ s)).symm (t ≫ g)) =
      t ≫ φ.toFun (s ≫ ringTestMap K σ.toAlgHom) ((φ.toFun s).symm g)
    have h := φ.symm.naturality t s g
    change (φ.toFun (t ≫ s)).symm (t ≫ g) = t ≫ (φ.toFun s).symm g at h
    rw [h, Category.assoc, φ.naturality]

theorem galoisTwist_toFun (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (splitGroup K n).X) :
    (galoisTwist φ σ).toFun s x =
      φ.toFun (s ≫ ringTestMap K σ.toAlgHom) ((φ.toFun s).symm x) :=
  rfl

/-- The twists compose along Galois translates: `ψ_{σσ'}(s) = ψ_σ'(s ≫ σ*) ∘ ψ_σ(s)`. -/
theorem galoisTwist_mul (σ σ' : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (splitGroup K n).X) :
    (galoisTwist φ (σ * σ')).toFun s x =
      (galoisTwist φ σ').toFun (s ≫ ringTestMap K σ.toAlgHom) ((galoisTwist φ σ).toFun s x) := by
  rw [galoisTwist_toFun, galoisTwist_toFun, galoisTwist_toFun, MulEquiv.symm_apply_apply]
  have h : ringTestMap K (σ * σ').toAlgHom =
      ringTestMap K σ.toAlgHom ≫ ringTestMap K σ'.toAlgHom := by
    rw [← ringTestMap_comp]
    rfl
  rw [h, Category.assoc]

end Twist

end EvenOrthogonalForm

end Langlands.GroupScheme
