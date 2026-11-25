/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# The Frobenius on the geometric fundamental group

Let `e` be an automorphism of a connected scheme `Y` and `t` a geometric point of `Y`. The
transport `e_*` of finite étale `Y`-schemes along `e` composed with the fibre functor at `t` is
again a fibre functor (it is the fibre functor at `t ≫ e⁻¹`,
`AlgebraicGeometry.Scheme.FiniteEtale.mapIsoFiberIso`), so there is a path
`τ : F_t ∘ e_* ≅ F_t`. It induces a map `σ : π₁(Y, t) → π₁(Y, t)` with `τ (g • x) = σ g • τ x`
(`AlgebraicGeometry.Scheme.FiniteEtale.transportConj`). A path between fibre functors is
determined on totally split objects: it carries the point of `e_* P` on the section `e⁻¹ ≫ σ` to
the point of `P` on the section `σ` (`AlgebraicGeometry.Scheme.FiniteEtale.transport_section`).

For the geometric Galois Frobenius `g` of the geometric fibre `C = C₀ ×_K K̄` of a scheme over a
finite field, the base change `b : FÉt(C₀) ⥤ FÉt(C)` satisfies `g_* ∘ b ≅ b`, so a path
`F_t ∘ b ≅ F_s` turns `τ` into an automorphism of the fibre functor `F_s` on `FÉt(C₀)`, that is an
element `w` of `π₁(C₀, s)`. It acts on the geometric fibres of the constant covers as the
geometric Frobenius (`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_frobeniusElement`), and
conjugation by it induces `σ` on the image of `π₁(C, t)`
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_transportConj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

section Transport

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
  (e : Y ≅ Y)

/-- The fibre functor at `t` precomposed with the transport `e_*` is the fibre functor at
`t ≫ e⁻¹`. -/
noncomputable def mapIsoFiberIso : FiniteEtale.mapIso e ⋙ fiber t ≅ fiber (t ≫ e.inv) :=
  NatIso.ofComponents (fun P ↦ FintypeCat.equivEquivIso
    { toFun y := fiberMk (t ≫ e.inv) P y.left (by
        have hy : y.left ≫ P.obj.hom ≫ e.hom = t := fiber_left_comp t y
        calc y.left ≫ P.obj.hom = (y.left ≫ P.obj.hom ≫ e.hom) ≫ e.inv := by simp
          _ = t ≫ e.inv := by rw [hy])
      invFun z := fiberMk t ((FiniteEtale.mapIso e).obj P) z.left (by
        change z.left ≫ P.obj.hom ≫ e.hom = t
        rw [← Category.assoc, fiber_left_comp (t ≫ e.inv) z, Category.assoc, e.inv_hom_id,
          Category.comp_id])
      left_inv y := fiber_ext t rfl
      right_inv z := fiber_ext _ rfl })
    (fun {P Q} φ ↦ FintypeCat.hom_ext _ _ fun y ↦ fiber_ext _ rfl)

variable [ConnectedSpace Y]

lemma nonempty_mapIso_fiber_iso : Nonempty (FiniteEtale.mapIso e ⋙ fiber t ≅ fiber t) :=
  ⟨mapIsoFiberIso t e ≪≫ (nonempty_iso_of_fiberFunctor (fiber (t ≫ e.inv)) (fiber t)).some⟩

/-- The terminal finite étale `Y`-scheme `Y ⟶ Y`. -/
noncomputable def unitFiniteEtale : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance, inferInstanceAs (IsFinite (𝟙 Y))⟩

variable {e} (τ : FiniteEtale.mapIso e ⋙ fiber t ≅ fiber t)

omit [ConnectedSpace Y] in
/-- A path `τ : F_t ∘ e_* ≅ F_t` carries the point of `e_* P` on the section `e⁻¹ ≫ σ` to the point
of `P` on the section `σ`: naturality with respect to the morphism `Y ⟶ P` given by `σ`, the
geometric fibres of `Y` and of `e_* Y` being points. -/
lemma transport_section (P : Y.FiniteEtale) (σ : Y ⟶ P.obj.left) (hσ : σ ≫ P.obj.hom = 𝟙 Y)
    (x : (fiber t).obj ((FiniteEtale.mapIso e).obj P)) (hx : x.left = t ≫ e.inv ≫ σ) :
    (τ.hom.app P x).left = t ≫ σ := by
  let T := unitFiniteEtale (Y := Y)
  let S : T ⟶ P := ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  let x₁ : (fiber t).obj ((FiniteEtale.mapIso e).obj T) := fiberMk t _ (t ≫ e.inv) (by
    change (t ≫ e.inv) ≫ 𝟙 Y ≫ e.hom = t
    simp)
  have hx₁ : (fiber t).map ((FiniteEtale.mapIso e).map S) x₁ = x := fiber_ext t <| by
    rw [fiber_map_left, hx]
    rfl
  have hn := ConcreteCategory.congr_hom (τ.hom.naturality S) x₁
  have key : τ.hom.app P x = (fiber t).map S (τ.hom.app T x₁) := by
    rw [← hx₁]
    exact hn
  have h₀ : (τ.hom.app T x₁).left = t := by
    rw [← Category.comp_id (τ.hom.app T x₁).left]
    exact fiber_left_comp t (τ.hom.app T x₁)
  rw [key, fiber_map_left, h₀]
  rfl

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber t).obj P)] [IsFundamentalGroup (fiber t) G]

/-- The automorphism of `π₁(Y, t)` induced by a path `τ : F_t ∘ e_* ≅ F_t`: the element acting on
the fibre functor as `τ ∘ g ∘ τ⁻¹`. -/
noncomputable def transportConj (g : G) : G :=
  (toAutMulEquiv (fiber t) G).symm
    (.of (τ.symm ≪≫ Functor.isoWhiskerLeft (FiniteEtale.mapIso e) (toAut (fiber t) G g).asIso ≪≫ τ))

lemma transportConj_smul (P : Y.FiniteEtale) (g : G)
    (x : (fiber t).obj ((FiniteEtale.mapIso e).obj P)) :
    τ.hom.app P (g • x) = transportConj t τ G g • τ.hom.app P x := by
  rw [← toAut_hom_app_apply (F := fiber t) (G := G)]
  change _ = ((toAutMulEquiv (fiber t) G) ((toAutMulEquiv (fiber t) G).symm _)).asIso.hom.app P _
  rw [MulEquiv.apply_symm_apply]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, FintypeCat.comp_apply]
  rw [toAut_hom_app_apply]
  congr 2
  exact (ConcreteCategory.congr_hom (τ.hom_inv_id_app P) x).symm

end Transport

section GeometricFiber

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K))

@[reassoc (attr := simp)]
lemma geometricGaloisFrobenius_inv_comp_geometricFiberProj :
    p.geometricGaloisFrobenius.asIso.inv ≫ p.geometricFiberProj = p.geometricFiberProj := by
  rw [Iso.inv_comp_eq, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]

@[reassoc (attr := simp)]
lemma geometricGaloisFrobenius_inv_comp_geometricFiberToAlgebraicClosure :
    p.geometricGaloisFrobenius.asIso.inv ≫ p.geometricFiberToAlgebraicClosure ≫
      (specGeometricFrobenius K).asIso.hom = p.geometricFiberToAlgebraicClosure := by
  rw [Iso.inv_comp_eq,
    Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure]

/-- The base change `b(P₀) = P₀ ×_{C₀} C` of a finite étale `C₀`-scheme to the geometric fibre is
isomorphic to its transport `g_* b(P₀)` along the geometric Galois Frobenius `g` of `C`, through
`1 ×_{C₀} g⁻¹`, since `g` lies over `C₀`. -/
noncomputable def pullbackMapIsoIso (P₀ : C.FiniteEtale) :
    (pullback p.geometricFiberProj).obj P₀ ≅
      (FiniteEtale.mapIso p.geometricGaloisFrobenius.asIso).obj
        ((pullback p.geometricFiberProj).obj P₀)
    where
  hom := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj (𝟙 _)
      p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp)
      (by rw [Category.comp_id, geometricGaloisFrobenius_inv_comp_geometricFiberProj]))
    (by
      change Limits.pullback.map _ _ _ _ _ _ _ _ _ ≫ Limits.pullback.snd _ _ ≫ _ = _
      simp))
  inv := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj (𝟙 _)
      p.geometricGaloisFrobenius.asIso.hom (𝟙 _) (by simp)
      (by rw [Category.comp_id, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]))
    (by
      change _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ≫ _
      simp))
  hom_inv_id := by
    apply hom_ext
    change Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp) (by simp) ≫
      Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.hom (𝟙 _) (by simp) (by simp) = 𝟙 _
    apply Limits.pullback.hom_ext <;> simp
  inv_hom_id := by
    apply hom_ext
    change Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.hom (𝟙 _) (by simp) (by simp) ≫
      Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp) (by simp) = 𝟙 _
    apply Limits.pullback.hom_ext <;> simp

lemma pullbackMapIsoIso_hom_naturality {P₀ Q₀ : C.FiniteEtale} (φ : P₀ ⟶ Q₀) :
    (pullback p.geometricFiberProj).map φ ≫ (pullbackMapIsoIso p Q₀).hom =
      (pullbackMapIsoIso p P₀).hom ≫
        (FiniteEtale.mapIso p.geometricGaloisFrobenius.asIso).map
          ((pullback p.geometricFiberProj).map φ) := by
  apply hom_ext
  change ((pullback p.geometricFiberProj).map φ).hom.left ≫
      Limits.pullback.map Q₀.obj.hom p.geometricFiberProj Q₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp) (by simp) =
    Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp) (by simp) ≫
      ((pullback p.geometricFiberProj).map φ).hom.left
  rw [pullback_map_hom_left]
  apply Limits.pullback.hom_ext <;> simp

lemma pullbackMapIsoIso_hom_hom_left (P₀ : C.FiniteEtale) :
    (pullbackMapIsoIso p P₀).hom.hom.left =
      Limits.pullback.map P₀.obj.hom p.geometricFiberProj P₀.obj.hom p.geometricFiberProj
        (𝟙 _) p.geometricGaloisFrobenius.asIso.inv (𝟙 _) (by simp) (by simp) :=
  rfl

omit [Finite K] in
lemma sectionOfPoint_congr (A : FiniteEtaleAlgebra K)
    {u u' : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1)} (h : u = u')
    (hu : u ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom)
    (hu' : u' ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom) :
    sectionOfPoint p A u hu = sectionOfPoint p A u' hu' := by
  subst h
  rfl

/-- The arithmetic Frobenius `x ↦ x ^ q` of a finite étale `K`-algebra `A`, acting on the
`K̄`-points of `Spec A` over `K`, is the inverse of the geometric Frobenius of `K̄`. -/
lemma comp_specMap_frobenius (A : FiniteEtaleAlgebra K)
    (u : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1)) :
    u ≫ Spec.map (CommRingCat.ofHom (A.frobenius : A.1 →+* A.1)) =
      (specGeometricFrobenius K).asIso.inv ≫ u := by
  let := Fintype.ofFinite K
  rw [Iso.eq_inv_comp, specGeometricFrobenius_hom, ← Spec.map_preimage u, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    RingHom.coe_coe, FiniteEtaleAlgebra.frobenius_apply, map_pow]
  rw [Nat.card_eq_fintype_card]
  set y := (Spec.preimage u).hom a
  have h : ∀ z : AlgebraicClosure K,
      z ^ Fintype.card K = FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) z :=
    fun _ ↦ rfl
  rw [h]
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).apply_symm_apply y

variable [ConnectedSpace C] [ConnectedSpace p.geometricFiber]
  {t : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber} {s : Spec (.of (AlgebraicClosure K)) ⟶ C}
  (τ : pullback p.geometricFiberProj ⋙ fiber t ≅ fiber s)
  (τF : FiniteEtale.mapIso p.geometricGaloisFrobenius.asIso ⋙ fiber t ≅ fiber t)

/-- The automorphism `F_s ≅ F_t ∘ b ≅ F_t ∘ g_* ∘ b ≅ F_t ∘ b ≅ F_s` of the fibre functor of
`C₀` induced by the transport `τF` along the geometric Galois Frobenius and the path `τ`. -/
noncomputable def frobeniusAut : fiber s ≅ fiber s :=
  τ.symm ≪≫ NatIso.ofComponents (F := pullback p.geometricFiberProj ⋙ fiber t)
    (G := pullback p.geometricFiberProj ⋙ fiber t)
    (fun P₀ ↦ (fiber t).mapIso (pullbackMapIsoIso p P₀) ≪≫
      τF.app ((pullback p.geometricFiberProj).obj P₀))
    (fun {P₀ Q₀} φ ↦ by
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        ← Category.assoc, ← Functor.map_comp, pullbackMapIsoIso_hom_naturality]
      rw [Functor.map_comp, Category.assoc, Category.assoc]
      congr 1
      exact τF.hom.naturality ((pullback p.geometricFiberProj).map φ)) ≪≫ τ

omit [ConnectedSpace C] [ConnectedSpace p.geometricFiber] in
lemma frobeniusAut_hom_app (P₀ : C.FiniteEtale)
    (z : (fiber t).obj ((pullback p.geometricFiberProj).obj P₀)) :
    (frobeniusAut p τ τF).hom.app P₀ (τ.hom.app P₀ z) =
      τ.hom.app P₀ (τF.hom.app _ ((fiber t).map (pullbackMapIsoIso p P₀).hom z)) := by
  simp only [frobeniusAut, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    FintypeCat.comp_apply]
  congr 3
  exact ConcreteCategory.congr_hom (τ.hom_inv_id_app P₀) z

variable (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [∀ P, MulAction G' ((fiber t).obj P)] [IsFundamentalGroup (fiber t) G']
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- The Frobenius element `w ∈ π₁(C₀, s)`: the element acting on the fibre functor as
`AlgebraicGeometry.Scheme.FiniteEtale.frobeniusAut`. -/
noncomputable def frobeniusElement : G :=
  (toAutMulEquiv (fiber s) G).symm (.of (frobeniusAut p τ τF))

omit [ConnectedSpace p.geometricFiber] in
lemma frobeniusElement_smul (P₀ : C.FiniteEtale) (y : (fiber s).obj P₀) :
    frobeniusElement p τ τF G • y = (frobeniusAut p τ τF).hom.app P₀ y := by
  rw [← toAut_hom_app_apply (F := fiber s) (G := G)]
  change ((toAutMulEquiv (fiber s) G) ((toAutMulEquiv (fiber s) G).symm _)).asIso.hom.app P₀ y = _
  rw [MulEquiv.apply_symm_apply]

omit [Finite K] in
lemma eq_of_forall_smul_eq {g h : G} (H : ∀ P (x : (fiber s).obj P), g • x = h • x) : g = h := by
  have := IsFundamentalGroup.non_trivial (F := fiber s) (h⁻¹ * g) fun X x ↦ by
    rw [mul_smul, H, inv_smul_smul]
  exact (inv_mul_eq_one.1 this).symm

/-- **The Frobenius of the geometric fibre is conjugation by the Frobenius element**: the
automorphism of `π₁(C₀ ×_K K̄, t)` induced by the transport along the geometric Galois Frobenius
corresponds, in `π₁(C₀, s)`, to conjugation by
`AlgebraicGeometry.Scheme.FiniteEtale.frobeniusElement`. -/
theorem fundamentalGroupMap_transportConj (k : G') :
    fundamentalGroupMap τ G' G (transportConj t τF G' k) =
      frobeniusElement p τ τF G * fundamentalGroupMap τ G' G k *
        (frobeniusElement p τ τF G)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  refine eq_of_forall_smul_eq (s := s) G fun P₀ y ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z, τ.hom.app P₀ z = y :=
    ⟨τ.inv.app P₀ y, ConcreteCategory.congr_hom (τ.inv_hom_id_app P₀) y⟩
  rw [mul_smul, mul_smul, frobeniusElement_smul, frobeniusAut_hom_app, fundamentalGroupMap_smul,
    fundamentalGroupMap_smul, frobeniusElement_smul, frobeniusAut_hom_app,
    ← transportConj_smul, ← IsNaturalSMul.naturality]

section ConstantCover

variable (A : FiniteEtaleAlgebra K)

omit [ConnectedSpace C] [ConnectedSpace p.geometricFiber] in
lemma sectionOfPoint_comp_pullbackMapIsoIso (u : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1))
    (hu : u ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom) :
    sectionOfPoint p A u hu ≫ (pullbackMapIsoIso p (constantCover p A)).hom.hom.left =
      p.geometricGaloisFrobenius.asIso.inv ≫
        sectionOfPoint p A ((specGeometricFrobenius K).asIso.hom ≫ u)
        (by rw [Category.assoc, hu, specGeometricFrobenius_hom_comp_specAlgebraicClosure]) := by
  rw [pullbackMapIsoIso_hom_hom_left]
  apply hom_ext_pullback_constantCover
  · simp [-constantCover_obj_hom]
  · simp [-constantCover_obj_hom]

omit [ConnectedSpace C] [ConnectedSpace p.geometricFiber] in
lemma sectionOfPoint_comp_arithmeticFrobenius
    (u : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1))
    (hu : u ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom) :
    sectionOfPoint p A u hu ≫
      ((pullback p.geometricFiberProj).map (arithmeticFrobenius p A).hom).hom.left =
      sectionOfPoint p A ((specGeometricFrobenius K).asIso.inv ≫ u)
        (by rw [Category.assoc, hu, Iso.inv_comp_eq,
          specGeometricFrobenius_hom_comp_specAlgebraicClosure]) := by
  rw [pullback_map_hom_left]
  apply hom_ext_pullback_constantCover
  · simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso, comp_specMap_frobenius]
  · simp [-constantCover_obj_hom]

end ConstantCover

omit [ConnectedSpace p.geometricFiber] in
/-- **The Frobenius element lies in the Weil group with degree one**: it acts on the geometric
fibres of the constant covers as the geometric Frobenius. Through the path `τ`, a point of the
fibre of `C₀ ×_K Spec A` is a point on the section of `(C₀ ×_K Spec A) ×_{C₀} C` attached to a
`K̄`-point `u` of `Spec A`; the transport along `g` carries it to the section attached to
`σ ≫ u`, `σ` the geometric Frobenius of `K̄`, which the arithmetic Frobenius of `A` carries back
to `u`. -/
theorem mem_weilGroup_frobeniusElement [GeometricallyConnected p]
    (ht : t ≫ p.geometricFiberToAlgebraicClosure = 𝟙 _) :
    (frobeniusElement p τ τF G, Multiplicative.ofAdd (1 : ℤ)) ∈ weilGroup p s G := by
  refine (mem_weilGroup_iff p s G).2 fun A y ↦ ?_
  simp only [toAdd_ofAdd, zpow_one]
  obtain ⟨z, rfl⟩ : ∃ z, τ.hom.app _ z = y :=
    ⟨τ.inv.app _ y, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) y⟩
  have hz := left_eq_sectionOfPoint p ht A z
  set u := pointOfFiber p A z
  have hu := pointOfFiber_comp_specHom p ht A z
  let x₁ := (fiber t).map (pullbackMapIsoIso p (constantCover p A)).hom z
  have hx₁ : x₁.left = t ≫ p.geometricGaloisFrobenius.asIso.inv ≫
      sectionOfPoint p A ((specGeometricFrobenius K).asIso.hom ≫ u)
        (by rw [Category.assoc, hu, specGeometricFrobenius_hom_comp_specAlgebraicClosure]) := by
    rw [fiber_map_left, hz, Category.assoc, sectionOfPoint_comp_pullbackMapIsoIso]
  have hz' := transport_section t τF _ _ (sectionOfPoint_snd p A _ _) x₁ hx₁
  set z' := τF.hom.app _ x₁
  have hz'' : (fiber t).map ((pullback p.geometricFiberProj).map (arithmeticFrobenius p A).hom)
      z' = z := by
    apply fiber_ext
    rw [fiber_map_left, hz', Category.assoc, sectionOfPoint_comp_arithmeticFrobenius, hz]
    congr 1
    exact sectionOfPoint_congr p A (Iso.inv_hom_id_assoc _ _) _ _
  have hy : (fiber s).map (arithmeticFrobenius p A).hom (τ.hom.app _ z') = τ.hom.app _ z := by
    rw [← hz'']
    exact (ConcreteCategory.congr_hom (τ.hom.naturality (arithmeticFrobenius p A).hom) z').symm
  have hinj : Function.Injective ((fiber s).map (arithmeticFrobenius p A).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  rw [frobeniusElement_smul, frobeniusAut_hom_app]
  apply hinj
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius]
  exact hy

end GeometricFiber

end AlgebraicGeometry.Scheme.FiniteEtale
