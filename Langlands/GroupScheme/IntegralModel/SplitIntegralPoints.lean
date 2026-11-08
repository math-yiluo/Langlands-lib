import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.GroupScheme.Reductive.LocalRootGroupParam

/-! # Integral points on closed root groups and closed split tori of an integral model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BasePoints

variable {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)

/-- Changing the base of a section and reading the result through the pullback point
correspondence is restriction of the section along `b`. -/
theorem baseChangePointsEquiv_baseChangeSectionHom (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangePointsEquiv b G (Over.mk (𝟙 T)) (baseChangeSectionHom b G x) =
      (Over.homMk b (by simp) : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S)) ≫ x := by
  apply Over.OverMorphism.ext
  change (baseChangeSectionHom b G x).left ≫ pullback.fst G.X.hom b = b ≫ x.left
  exact baseChangeSectionHom_fst b G x

end BasePoints

namespace IntegralModel

open LocalSplitCell LocalSplitBigCell

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-! ### Root groups -/

/-- The generic fibre of an integral map `u : 𝔾ₐ ⟶ M.group`, with the standard `𝔾ₐ` over `K`
as source, followed by the supplied generic identification of the model. -/
def genericRootHom (u : Ga R ⟶ M.group) : Ga K ⟶ G :=
  (gaIso (R := R) K).inv ≫ M.genericHom u

omit [IsDomain R] [IsFractionRing R K] in
/-- Base change of the integral `𝔾ₐ`-point with coordinate `r` is the `𝔾ₐ`-point with the
restricted coordinate. -/
theorem baseChangeSectionHom_scalarPoint (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    baseChangeSectionHom (Spec.algebraMap R K) (Ga R)
        (VectorGroup.scalarPoint (CommRingCat.of R) (Over.mk (𝟙 _)) r) =
      VectorGroup.scalarPoint (CommRingCat.of K) (Over.mk (𝟙 _))
          ((Spec.algebraMap R K).appTop r) ≫ (gaIso (R := R) K).inv.hom.hom := by
  apply (baseChangePointsEquiv (Spec.algebraMap R K) (Ga R) (Over.mk (𝟙 _))).injective
  rw [baseChangePointsEquiv_baseChangeSectionHom, VectorGroup.scalarPoint_comp]
  exact (LocalSplitBigCell.baseChangePointsEquiv_scalarPoint K (Over.mk (𝟙 _)) _).symm

/-- The integral section `u(r)` is sent by the integral-point map to the generic root value
at the restricted coordinate. -/
theorem integralPointMap_rootPoint (u : Ga R ⟶ M.group) (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    M.integralPointMap (rootPoint u (Over.mk (𝟙 _)) r) =
      rootPoint (M.genericRootHom u) (Over.mk (𝟙 _)) ((Spec.algebraMap R K).appTop r) := by
  change M.subgroupPointMap u (VectorGroup.scalarPoint (CommRingCat.of R) (Over.mk (𝟙 _)) r) = _
  rw [subgroupPointMap_apply, baseChangeSectionHom_scalarPoint]
  change _ = VectorGroup.scalarPoint (CommRingCat.of K) (Over.mk (𝟙 _)) _ ≫
    ((gaIso (R := R) K).inv ≫ M.genericHom u).hom.hom
  rw [Grp.comp_hom_hom, ← Category.assoc]
  rfl

/-- **Integral points of a closed root group.** For a closed subgroup `u : 𝔾ₐ ⟶ M.group`, the
generic value `u(c)` at a global function `c` on `Spec K` is an integral point of the model
exactly when `c` is the restriction of a global function on `Spec R`. -/
theorem rootPoint_genericRootHom_mem_integralPoints_iff (u : Ga R ⟶ M.group)
    (hu : IsClosedSubgroup u) (c : Γ(Spec (CommRingCat.of K), ⊤)) :
    rootPoint (M.genericRootHom u) (Over.mk (𝟙 _)) c ∈ M.integralPoints ↔
      ∃ r : Γ(Spec (CommRingCat.of R), ⊤), (Spec.algebraMap R K).appTop r = c := by
  constructor
  · rintro ⟨x, hx⟩
    have hxy : M.integralPointMap x = rationalPoints.map (M.genericHom u)
        (VectorGroup.scalarPoint (CommRingCat.of K) (Over.mk (𝟙 _)) c ≫
          (gaIso (R := R) K).inv.hom.hom) := by
      rw [hx]
      change _ ≫ ((gaIso (R := R) K).inv ≫ M.genericHom u).hom.hom = _
      rw [Grp.comp_hom_hom, ← Category.assoc]
      rfl
    obtain ⟨h, -, hh⟩ := M.exists_eq_of_integralPointMap_eq u hu x _ hxy
    obtain ⟨r, rfl⟩ := (LocalRootGroup.scalarPoint_bijective (CommRingCat.of R)
      (Over.mk (𝟙 _))).2 h
    refine ⟨r, ?_⟩
    rw [baseChangeSectionHom_scalarPoint] at hh
    have hh' := congrArg (fun y => y ≫ (gaIso (R := R) K).hom.hom.hom) hh
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id] at hh'
    exact (LocalRootGroup.scalarPoint_bijective (CommRingCat.of K) (Over.mk (𝟙 _))).1 hh'
  · rintro ⟨r, rfl⟩
    exact ⟨rootPoint u (Over.mk (𝟙 _)) r, M.integralPointMap_rootPoint u r⟩

/-- The generic root value at an element of the field `K`. -/
def genericRootValue (u : Ga R ⟶ M.group) (c : K) : rationalPoints G :=
  rootPoint (M.genericRootHom u) (Over.mk (𝟙 _)) ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)

/-- **Integral points of a closed root group, field form.** The generic value `u(c)`, `c ∈ K`,
is an integral point of the model exactly when `c` lies in the image of `R`. -/
theorem genericRootValue_mem_integralPoints_iff (u : Ga R ⟶ M.group)
    (hu : IsClosedSubgroup u) (c : K) :
    M.genericRootValue u c ∈ M.integralPoints ↔ c ∈ (algebraMap R K).range := by
  rw [genericRootValue, M.rootPoint_genericRootHom_mem_integralPoints_iff u hu]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r, ?_⟩
    have h := congrArg (fun f => f.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Spec.algebraMap R K).appTop r) =
      algebraMap R K ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) at h
    rw [← h, hr]
    exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c
  · rintro ⟨r, rfl⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv r, ?_⟩
    have h := congrArg (fun f => f.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    exact h.symm

/-! ### Split tori -/

variable {I : Type u} [Finite I]

/-- The generic fibre of an integral map from the split torus on `I`, with the split torus on
`I` over `K` as source, followed by the supplied generic identification of the model. -/
def genericSplitTorusHom (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group) :
    splitTorus (Spec (CommRingCat.of K)) I ⟶ G :=
  (splitTorus.baseChangeIso (Spec.algebraMap R K) I).inv ≫ M.genericHom i

omit [IsDomain R] [IsFractionRing R K] in
/-- Base change of an integral point of a split torus has the restricted unit coordinates. -/
theorem pointsEquiv_baseChangeSectionHom
    (h : rationalPoints (splitTorus (Spec (CommRingCat.of R)) I)) :
    splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (baseChangeSectionHom (Spec.algebraMap R K) _ h ≫
          (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom) =
      fun j => Units.map (Spec.algebraMap R K).appTop.hom.toMonoidHom
        (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of R)))) h j) := by
  rw [splitTorus.pointsEquiv_baseChangeIso_hom, splitTorus.baseChangePointsEquiv,
    MulEquiv.trans_apply, baseChangePointsEquiv_baseChangeSectionHom,
    splitTorus.pointsEquiv_naturality]
  rfl

/-- **Integral points of a closed split torus.** For a closed subgroup
`i : splitTorus (Spec R) I ⟶ M.group`, the generic image of the `K`-point with unit
coordinates `t` is an integral point of the model exactly when every coordinate of `t` is the
restriction of a unit on `Spec R`. -/
theorem splitTorusPoint_mem_integralPoints_iff
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group) (hi : IsClosedSubgroup i)
    (t : I → (Γ(Spec (CommRingCat.of K), ⊤))ˣ) :
    (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm t ≫
        (M.genericSplitTorusHom i).hom.hom ∈ M.integralPoints ↔
      ∀ j, ∃ s : (Γ(Spec (CommRingCat.of R), ⊤))ˣ,
        Units.map (Spec.algebraMap R K).appTop.hom.toMonoidHom s = t j := by
  set y := (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm t ≫
    (splitTorus.baseChangeIso (Spec.algebraMap R K) I).inv.hom.hom with hy
  have hyt : splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))
      (y ≫ (splitTorus.baseChangeIso (Spec.algebraMap R K) I).hom.hom.hom) = t := by
    rw [hy, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id, MulEquiv.apply_symm_apply]
  have hpt : (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm t ≫
      (M.genericSplitTorusHom i).hom.hom = rationalPoints.map (M.genericHom i) y := by
    change _ ≫ ((splitTorus.baseChangeIso (Spec.algebraMap R K) I).inv ≫
      M.genericHom i).hom.hom = _
    rw [Grp.comp_hom_hom, ← Category.assoc]
    rfl
  rw [hpt]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h, -, hh⟩ := M.exists_eq_of_integralPointMap_eq i hi x y hx
    intro j
    refine ⟨splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of R)))) h j, ?_⟩
    have := congrFun (pointsEquiv_baseChangeSectionHom (K := K) h) j
    rw [hh, hyt] at this
    exact this.symm
  · intro ht
    choose s hs using ht
    let h : rationalPoints (splitTorus (Spec (CommRingCat.of R)) I) :=
      (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of R))))).symm s
    have hhy : baseChangeSectionHom (Spec.algebraMap R K) _ h = y := by
      apply (isoPointsEquiv (splitTorus.baseChangeIso (Spec.algebraMap R K) I)
        (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
      apply (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
      rw [isoPointsEquiv_apply, isoPointsEquiv_apply, pointsEquiv_baseChangeSectionHom, hyt]
      funext j
      rw [MulEquiv.apply_symm_apply, hs]
    refine ⟨rationalPoints.map i h, ?_⟩
    rw [← hhy]
    exact M.subgroupPointMap_apply i h

/-- The generic image of the `K`-point of the split torus with field unit coordinates `t`. -/
def genericSplitTorusValue (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group)
    (t : I → Kˣ) : rationalPoints G :=
  (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm
      (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom (t j)) ≫
    (M.genericSplitTorusHom i).hom.hom

/-- **Integral points of a closed split torus, field form.** The generic image of the torus
point with coordinates `t : I → Kˣ` is an integral point of the model exactly when every
coordinate is the image of a unit of `R`. -/
theorem genericSplitTorusValue_mem_integralPoints_iff
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group) (hi : IsClosedSubgroup i)
    (t : I → Kˣ) :
    M.genericSplitTorusValue i t ∈ M.integralPoints ↔
      ∀ j, ∃ s : Rˣ, Units.map (algebraMap R K : R →* K) s = t j := by
  rw [genericSplitTorusValue, M.splitTorusPoint_mem_integralPoints_iff i hi]
  have hnat : ∀ r : Γ(Spec (CommRingCat.of R), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Spec.algebraMap R K).appTop r) =
        algebraMap R K ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) := fun r =>
    congrArg (fun f => f.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
  refine forall_congr' fun j => ?_
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom s, ?_⟩
    apply Units.ext
    have := congrArg (fun w : (Γ(Spec (CommRingCat.of K), ⊤))ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (w : Γ(Spec (CommRingCat.of K), ⊤))) hs
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        ((Spec.algebraMap R K).appTop (s : Γ(Spec (CommRingCat.of R), ⊤))) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (t j : K)) at this
    change algebraMap R K ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (s : Γ(Spec (CommRingCat.of R), ⊤))) = (t j : K)
    rw [← hnat, this]
    exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply _
  · rintro ⟨s, hs⟩
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom s, ?_⟩
    apply Units.ext
    apply (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Spec.algebraMap R K).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s : R))) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (t j : K))
    rw [hnat, (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply,
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply, ← hs]
    rfl

end IntegralModel

end Langlands.GroupScheme
