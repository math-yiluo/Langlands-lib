/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.RingTheory.DualNumber

/-!
# Points of a group scheme with values in local rings

Let `G` be a group scheme over a field `k`, with identity point `1 ∈ G` and local ring `𝒪_{G,1}`
there. A point `p : Spec A ⟶ G` with values in a local `k`-algebra `A` which sends the closed point
to `1` is determined by the local homomorphism `p^♯ : 𝒪_{G,1} → A`
(`AlgebraicGeometry.GrpObj.pointStalkHom`), and base change along a local homomorphism `ψ : A → B`
composes `p^♯` with `ψ`. Conversely a local homomorphism `𝒪_{G,1} → B` which becomes the
homomorphism of a point after composing with an injective `B → A` is itself the homomorphism of a
point.

For a local `k`-algebra `A` with a residue map `π : A → k`, the points of `G` with values in `A`
reducing to the identity along `π` form a subgroup `AlgebraicGeometry.GrpObj.pointsKer G π`, on
which `p ↦ p^♯` is injective (`AlgebraicGeometry.GrpObj.kerHom`). For the dual numbers this
subgroup is the tangent group. These descriptions are used to compute the Lie bracket.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The local ring `𝒪_{G,1}` of a group scheme at its identity point. -/
noncomputable abbrev stalkOne : CommRingCat.{u} :=
  G.left.presheaf.stalk (onePoint G)

/-- The identity point of `G(k)` sends the point of `Spec k` to the identity point. -/
theorem one_left_apply (x : Spec (.of k)) : (1 : points G k).left x = onePoint G := by
  rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum k) _ _)

variable {G} {A B : Type u} [CommRing A] [Algebra k A] [IsLocalRing A] [CommRing B] [Algebra k B]
  [IsLocalRing B]

/-- The local homomorphism `p^♯ : 𝒪_{G,1} ⟶ A` of a point `p : Spec A ⟶ G` with values in a local
ring sending the closed point to the identity point. -/
noncomputable def pointStalkHom (p : points G A) (hp : p.left (closedPoint A) = onePoint G) :
    stalkOne G ⟶ CommRingCat.of A :=
  (G.left.presheaf.stalkCongr (.of_eq hp.symm)).hom ≫
    Scheme.stalkClosedPointTo (p.left : Spec (.of A) ⟶ G.left)

instance (p : points G A) (hp : p.left (closedPoint A) = onePoint G) :
    IsLocalHom (pointStalkHom p hp).hom := by
  have := isLocalHom_of_isIso (G.left.presheaf.stalkCongr (.of_eq hp.symm)).hom
  have := Scheme.isLocalHom_stalkClosedPointTo (p.left : Spec (.of A) ⟶ G.left)
  rw [pointStalkHom, CommRingCat.hom_comp]
  exact RingHom.isLocalHom_comp _ _

omit [GrpObj G] in
theorem map_closedPoint (ψ : A →ₐ[k] B) [IsLocalHom ψ.toRingHom] (p : points G A) :
    (points.map G ψ p).left (closedPoint B) = p.left (closedPoint A) := by
  change p.left (Spec.map (CommRingCat.ofHom ψ.toRingHom) (closedPoint B)) = _
  have : IsLocalHom (CommRingCat.ofHom ψ.toRingHom).hom := ‹_›
  rw [Spec_closedPoint]

/-- Base change along a local homomorphism `ψ : A → B` composes `p^♯` with `ψ`. -/
theorem pointStalkHom_map (ψ : A →ₐ[k] B) [IsLocalHom ψ.toRingHom] (p : points G A)
    (hp : p.left (closedPoint A) = onePoint G)
    (hp' : (points.map G ψ p).left (closedPoint B) = onePoint G) :
    pointStalkHom (points.map G ψ p) hp' =
      pointStalkHom p hp ≫ CommRingCat.ofHom ψ.toRingHom := by
  have : IsLocalHom (CommRingCat.ofHom ψ.toRingHom).hom := ‹_›
  change (G.left.presheaf.stalkCongr _).hom ≫
    Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ p.left) = _
  rw [Scheme.stalkClosedPointTo_spec_map_comp, pointStalkHom]
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]

/-- A point with values in a local ring sending the closed point to the identity point is
determined by its homomorphism on `𝒪_{G,1}`. -/
theorem eq_of_pointStalkHom_eq {p q : points G A} (hp : p.left (closedPoint A) = onePoint G)
    (hq : q.left (closedPoint A) = onePoint G) (h : pointStalkHom p hp = pointStalkHom q hq) :
    p = q := by
  apply Over.OverMorphism.ext
  refine Scheme.eq_of_stalkClosedPointTo_eq (hp.trans hq.symm) ?_
  rw [pointStalkHom, pointStalkHom, ← Iso.eq_inv_comp] at h
  rw [h]
  simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]

/-- A local homomorphism `φ : 𝒪_{G,1} → B` which, after composing with an injective
homomorphism `ψ : B → A`, is the homomorphism of a point `q` of `G` with values in `A`, is the
homomorphism of a point `p` with values in `B`, and `q` is the base change of `p`. -/
theorem exists_pointStalkHom_eq (ψ : B →ₐ[k] A) (hψ : Function.Injective ψ)
    [IsLocalHom ψ.toRingHom] (q : points G A) (hq : q.left (closedPoint A) = onePoint G)
    (φ : stalkOne G ⟶ CommRingCat.of B) [IsLocalHom φ.hom]
    (h : pointStalkHom q hq = φ ≫ CommRingCat.ofHom ψ.toRingHom) :
    ∃ (p : points G B) (hp : p.left (closedPoint B) = onePoint G),
      pointStalkHom p hp = φ ∧ points.map G ψ p = q := by
  have : IsLocalHom (CommRingCat.ofHom ψ.toRingHom).hom := ‹_›
  obtain ⟨f, hfdef⟩ : ∃ f : Spec (.of B) ⟶ G.left,
      f = Spec.map φ ≫ G.left.fromSpecStalk (onePoint G) := ⟨_, rfl⟩
  have hf : f (closedPoint B) = onePoint G := by
    rw [hfdef, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hfq : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ f = q.left := by
    refine Scheme.eq_of_stalkClosedPointTo_eq (by
      rw [Scheme.Hom.comp_apply, Spec_closedPoint]; exact hf.trans hq.symm) ?_
    rw [Scheme.stalkClosedPointTo_spec_map_comp]
    subst hfdef
    rw [Scheme.stalkClosedPointTo_spec_map_fromSpecStalk]
    rw [pointStalkHom, ← Iso.eq_inv_comp] at h
    rw [h]
    simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom, Category.assoc,
      TopCat.Presheaf.stalkSpecializes_comp_assoc]
  have hover : f ≫ G.hom = ((Spec (.of B)).asOver (Spec (.of k))).hom := by
    have e : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ f ≫ G.hom =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ((Spec (.of B)).asOver (Spec (.of k))).hom := by
      rw [reassoc_of% hfq, Over.w q]
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (ψ.commutes x).symm
    rw [← Spec.map_preimage (f ≫ G.hom),
      ← Spec.map_preimage ((Spec (.of B)).asOver (Spec (.of k))).hom, ← Spec.map_comp,
      ← Spec.map_comp] at e
    have e' := Spec.map_injective e
    rw [← Spec.map_preimage (f ≫ G.hom),
      ← Spec.map_preimage ((Spec (.of B)).asOver (Spec (.of k))).hom]
    congr 1
    ext x
    exact hψ congr($e' x)
  refine ⟨Over.homMk f hover, hf, ?_, Over.OverMorphism.ext hfq⟩
  change (G.left.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo f = φ
  subst hfdef
  rw [Scheme.stalkClosedPointTo_spec_map_fromSpecStalk]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_comp_assoc,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

omit [IsLocalRing A] [IsLocalRing B] in
omit [GrpObj G] in
theorem _root_.AlgebraicGeometry.points.map_map {C : Type u} [CommRing C] [Algebra k C]
    (φ : A →ₐ[k] B) (φ' : B →ₐ[k] C) (x : points G A) :
    points.map G φ' (points.map G φ x) = points.map G (φ'.comp φ) x := by
  simp only [points.map, ← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-! ### Points reducing to the identity -/

variable (G) in
/-- The points of `G` with values in a local `k`-algebra `A` reducing to the identity along a
residue map `π : A → k`: the kernel of `G(A) → G(k)`. For the dual numbers it is the tangent
group. -/
noncomputable def pointsKer (π : A →ₐ[k] k) : Subgroup (points G A) :=
  (pointsPrecomp G ((Spec.map (CommRingCat.ofHom π.toRingHom)).asOver (Spec (.of k)))).ker

omit [IsLocalRing A] in
theorem mem_pointsKer {π : A →ₐ[k] k} {p : points G A} :
    p ∈ pointsKer G π ↔ points.map G π p = 1 :=
  MonoidHom.mem_ker

/-- A point reducing to the identity sends the closed point to the identity point. -/
theorem closedPoint_eq_onePoint {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] {p : points G A}
    (hp : p ∈ pointsKer G π) : p.left (closedPoint A) = onePoint G := by
  rw [← map_closedPoint π p, mem_pointsKer.1 hp, one_left_apply]

/-- The homomorphism `p^♯ : 𝒪_{G,1} → A` of a point reducing to the identity. -/
noncomputable def kerHom {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (p : pointsKer G π) :
    stalkOne G →+* A :=
  (pointStalkHom p.1 (closedPoint_eq_onePoint p.2)).hom

theorem kerHom_injective {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] :
    Function.Injective (kerHom (G := G) (π := π)) := fun _ _ h ↦
  Subtype.ext (eq_of_pointStalkHom_eq _ _ (CommRingCat.hom_ext h))

omit [IsLocalRing A] [IsLocalRing B] in
theorem map_mem_pointsKer {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B)
    (hψ : πB.comp ψ = πA) {p : points G A} (hp : p ∈ pointsKer G πA) :
    points.map G ψ p ∈ pointsKer G πB := by
  rw [mem_pointsKer] at hp ⊢
  rw [← hp, points.map_map, hψ]

/-- Base change along `ψ : A → B` compatible with the residue maps, as a homomorphism of the
groups of points reducing to the identity. -/
noncomputable def kerMap {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B)
    (hψ : πB.comp ψ = πA) : pointsKer G πA →* pointsKer G πB where
  toFun p := ⟨points.map G ψ p.1, map_mem_pointsKer ψ hψ p.2⟩
  map_one' := Subtype.ext (MonObj.comp_one _)
  map_mul' _ _ := Subtype.ext (MonObj.comp_mul _ _ _)

omit [IsLocalRing A] [IsLocalRing B] in
@[simp]
theorem coe_kerMap {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA)
    (p : pointsKer G πA) : (kerMap ψ hψ p : points G B) = points.map G ψ p.1 :=
  rfl

omit [IsLocalRing A] [IsLocalRing B] in
theorem isLocalHom_of_comp_eq {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} [IsLocalHom πA.toRingHom]
    (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA) : IsLocalHom ψ.toRingHom := by
  have : IsLocalHom (πB.toRingHom.comp ψ.toRingHom) := by
    have e : πB.toRingHom.comp ψ.toRingHom = πA.toRingHom := congrArg AlgHom.toRingHom hψ
    rw [e]
    infer_instance
  exact isLocalHom_of_comp _ πB.toRingHom

theorem kerHom_kerMap {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} [IsLocalHom πA.toRingHom]
    [IsLocalHom πB.toRingHom] (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA) (p : pointsKer G πA) :
    kerHom (kerMap ψ hψ p) = ψ.toRingHom.comp (kerHom p) := by
  have := isLocalHom_of_comp_eq ψ hψ
  exact congrArg CommRingCat.Hom.hom (pointStalkHom_map ψ _ _ _)

omit [IsLocalRing A] [IsLocalRing B] in
theorem kerMap_kerMap {C : Type u} [CommRing C] [Algebra k C] {πA : A →ₐ[k] k} {πB : B →ₐ[k] k}
    {πC : C →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA) (ψ' : B →ₐ[k] C)
    (hψ' : πC.comp ψ' = πB) (p : pointsKer G πA) :
    kerMap ψ' hψ' (kerMap ψ hψ p) = kerMap (ψ'.comp ψ) (by rw [← AlgHom.comp_assoc, hψ', hψ]) p :=
  Subtype.ext (points.map_map ψ ψ' p.1)

omit [IsLocalRing A] [IsLocalRing B] in
theorem kerMap_congr {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} {ψ ψ' : A →ₐ[k] B} (h : ψ = ψ')
    (hψ : πB.comp ψ = πA) (hψ' : πB.comp ψ' = πA) : kerMap (G := G) ψ hψ = kerMap ψ' hψ' := by
  subst h
  rfl

omit [IsLocalRing A] in
theorem kerMap_id {πA : A →ₐ[k] k} (p : pointsKer G πA) :
    kerMap (AlgHom.id k A) (AlgHom.comp_id πA) p = p := by
  apply Subtype.ext
  change points.map G (AlgHom.id k A) p.1 = p.1
  rw [points.map]
  convert Category.id_comp p.1
  ext1
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
  exact Spec.map_id _

omit [IsLocalRing A] [IsLocalRing B] in
/-- Base change along a homomorphism `A → B` factoring through the residue map `A → k` kills the
points reducing to the identity. -/
theorem kerMap_eq_one {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B)
    (h : ψ = (Algebra.ofId k B).comp πA) (hψ : πB.comp ψ = πA) (p : pointsKer G πA) :
    kerMap ψ hψ p = 1 := by
  apply Subtype.ext
  change points.map G ψ p.1 = 1
  rw [h, ← points.map_map, mem_pointsKer.1 p.2]
  exact MonObj.comp_one _

theorem kerMap_injective {πA : A →ₐ[k] k} {πB : B →ₐ[k] k} [IsLocalHom πA.toRingHom]
    [IsLocalHom πB.toRingHom] (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA)
    (hinj : Function.Injective ψ) : Function.Injective (kerMap (G := G) ψ hψ) := fun p q h ↦ by
  apply kerHom_injective
  ext a
  apply hinj
  have := congrArg (fun r ↦ kerHom r a) h
  simpa [kerHom_kerMap] using this

/-- The residue map `𝒪_{G,1} → k` of the local ring at the identity. -/
noncomputable def counit (G : Over (Spec (.of k))) [GrpObj G] : stalkOne G →+* k :=
  kerHom (1 : pointsKer G (AlgHom.id k k))

theorem kerHom_one {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] :
    kerHom (1 : pointsKer G π) = (algebraMap k A).comp (counit G) := by
  have h : π.comp (Algebra.ofId k A) = AlgHom.id k k := AlgHom.ext fun x ↦ by simp
  have := isLocalHom_of_comp_eq (Algebra.ofId k A) h
  rw [← map_one (kerMap (G := G) (Algebra.ofId k A) h), kerHom_kerMap]
  rfl

/-- A point reducing to the identity has the residue map of `𝒪_{G,1}` as reduction. -/
theorem kerHom_comp {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (p : pointsKer G π) :
    π.toRingHom.comp (kerHom p) = counit G := by
  rw [← kerHom_kerMap π (AlgHom.id_comp π) p]
  congr 1
  exact Subtype.ext (mem_pointsKer.1 p.2)

theorem kerHom_apply_of_mem_ker {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (p : pointsKer G π)
    (a : stalkOne G) : π (kerHom p a) = counit G a :=
  congrArg (fun f : stalkOne G →+* k ↦ f a) (kerHom_comp p)

end AlgebraicGeometry.GrpObj
