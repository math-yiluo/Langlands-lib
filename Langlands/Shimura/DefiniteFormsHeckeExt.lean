import Langlands.Shimura.DefiniteFormsSmoothExt
import Langlands.Shimura.LevelHeckeAlgebra
import Langlands.Shimura.LevelHeckeCompose
import Langlands.Cohomology.RightDerivedAdditive
import Langlands.Cohomology.HyperextAbutmentFunctor
import Langlands.Cohomology.DivisibleSystem.ScalarExtension

/-!
# Hecke operators on forms with trivial coefficients and on their Ext

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p.309,
Proposition 4.4, says that "as `K(N,m)^p` varies the spectral sequences are
`GG(𝔸_f^p)`-equivariant". At a fixed level `K` away from `p`, this equivariance is the action of
the double-coset operators `[K g L]` and of the Hecke algebra of `K`. This file constructs these
operators on the forms of level `e⁻¹ (1 × K)`, on their smooth parts, on `Ext^i(W, -)` of the
smooth parts, and on the intended abutment `Hom(X, A(K)[n])` with its filtration steps and graded
pieces, and shows that the maps of the presheaves of `DefiniteFormsSmoothExt` along arrows of
levels are such operators. The operators and the Hecke algebra are the published
`LevelHecke.heckeOperator`, `LevelHeckeAlgebra` and `LevelHecke.heckeAct` of the representation of
`H'` by right translation on the forms of trivial level. It does not show that the differentials
of the spectral sequence or the identification of its second page commute with these operators,
and does not treat forms with coefficients or the Galois action.

## Main definitions

For groups `Γ`, `G` with `ι : Γ →* G` and an isomorphism of topological groups
`e : G ≃ₜ* H × H'`, in the namespace `EquivariantForms`:

* `awayTranslation R e ι V`: right translation `(h • f) g = f (g * e⁻¹ (1, h))` by `H'` on the
  forms of trivial level; `awayFormsFixedEquiv` identifies its vectors fixed by `K'` with the
  forms of level `e⁻¹ (1 × K')`.
* `awayHecke R e ι V K L g`: the operator `[K g L]` from forms of level `e⁻¹ (1 × L)` to forms of
  level `e⁻¹ (1 × K)`, `([K g L] f) x = ∑ f (x * e⁻¹ (1, k g))` over representatives `k` of
  `K / (K ∩ g L g⁻¹)` (`awayHecke_apply_coe`); it commutes with right translation by `H`.
* `factorHeckeHom`, `factorSmoothHeckeHom`, `factorExtHecke`, `factorAbutmentHecke`,
  `factorFiltrationHecke`, `factorGradedHecke`: the operator `[K g L]` between the values at `L`
  and at `K` of `factorFormsPresheaf`, `factorSmoothPresheaf`, `factorExtPresheaf W i`,
  `factorAbutmentPresheaf X n`, `factorFiltrationPresheaf X n p` and
  `factorGradedPresheaf X n p`. The lemmas `factorFormsPresheaf_map_eq` and its analogues say
  that the map of each presheaf along an arrow `a : K ⟶ L` is `[K a L]` of its element.
* `formsHeckeAlgebraHom`, `smoothHeckeAlgebraHom`, `extHeckeAlgebraHom`,
  `abutmentHeckeAlgebraHom`, `filtrationHeckeAlgebraHom`, `gradedHeckeAlgebraHom`: the Hecke
  algebra of `K` acting on the values at `K` of these presheaves, as ring homomorphisms to their
  endomorphisms; the element `doubleCoset K g` acts by `[K g K]`
  (`formsHeckeAlgebraHom_doubleCoset` and its analogues).

In the namespace `HyperextAbutment`, `filtrationFunctor_additive` and `gradedFunctor_additive`
say that the functors of `HyperextAbutmentFunctor` are additive; `EquivariantForms.endRingHom`
is the ring homomorphism on endomorphisms given by an additive functor.

In the namespace `DefiniteForms`, for `σ : AlgebraInvolution ℚ A`, `p ≠ 0` and the published
splitting `σ.finiteAdelicPointsSplit p hp : GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`:
`dividingSmoothHecke`, `dividingSmoothHeckeAlgebraHom`, `dividingExtHecke`,
`dividingExtHeckeAlgebraHom`, `dividingAbutmentHecke`, `dividingAbutmentHeckeAlgebraHom`,
`dividingFiltrationHeckeAlgebraHom` and `dividingGradedHeckeAlgebraHom`, for `g ∈ GJ(𝔸_f^{(p)})`
and compact open levels `K`, `L` of `GJ(𝔸_f^{(p)})`.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel Langlands.Shimura.LevelHecke

universe t uR uΓ uG uH uH' u w

section EndRingHom

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- For an additive functor `F`, the map `F.map` on endomorphisms as a ring homomorphism. -/
def endRingHom (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) :=
  { F.mapEnd X with
    map_zero' := F.map_zero X X
    map_add' := fun _ _ => F.map_add }

@[simp]
lemma endRingHom_apply (F : C ⥤ D) [F.Additive] (X : C) (f : End X) :
    endRingHom F X f = F.map f :=
  rfl

end EndRingHom

section Translation

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) (V : Type t) [AddCommGroup V]
  [Module R V]

/-- Right translation `(h • f) g = f (g * e⁻¹ (1, h))` by the second factor `H'` on the forms of
trivial level `e⁻¹ (1 × ⊥) = ⊥`: the published `rightTranslation` along `awayHom e`. -/
def awayTranslation : Representation R H' (awayLevelForms R e ι V ⊥) :=
  rightTranslation ι _ _ (awayHom e) fun h k => by
    obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
    rw [Subgroup.mem_bot] at ha
    subst ha
    rw [← hak, map_one, mul_one, one_mul]

@[simp]
lemma awayTranslation_apply_coe (h : H') (f : awayLevelForms R e ι V ⊥) (g : G) :
    (awayTranslation R e ι V h f).1 g = f.1 (g * awayHom e h) :=
  rfl

/-- Right translation by `h ∈ H` on the forms of trivial level commutes with `awayTranslation`. -/
def factorTranslationIntertwining (h : H) :
    (awayTranslation R e ι V).IntertwiningMap (awayTranslation R e ι V) where
  toLinearMap := factorTranslation R e ι V ⊥ h
  isIntertwining' h' := by
    ext f x
    change f.1 (x * factorHom e h * awayHom e h') = f.1 (x * awayHom e h' * factorHom e h)
    rw [mul_assoc, mul_assoc, (factorHom_commute_awayHom e h h').eq]

/-- The vectors of `awayTranslation` fixed by a subgroup `K'` of `H'` are the forms of level
`e⁻¹ (1 × K')`. -/
def awayFormsFixedEquiv (K' : Subgroup H') :
    fixedVectors (awayTranslation R e ι V) K' ≃ₗ[R] awayLevelForms R e ι V K' where
  toFun f := ⟨f.1.1, f.1.2.1, fun g k => by
      obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
      have h := congrArg (fun f' : awayLevelForms R e ι V ⊥ => f'.1 g) (f.2 ⟨a, ha⟩)
      change f.1.1 (g * awayHom e a) = f.1.1 g at h
      change f.1.1 (g * k) = f.1.1 g
      rw [← hak, h]⟩
  invFun f := ⟨⟨f.1, f.2.1, fun g k => by
      obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
      rw [Subgroup.mem_bot] at ha
      subst ha
      change f.1 (g * k) = f.1 g
      rw [← hak, map_one, mul_one]⟩,
    fun k => Subtype.ext (funext fun g => f.2.2 g ⟨_, awayHom_mem_awayLevel e k.2⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma awayFormsFixedEquiv_apply_coe (K' : Subgroup H')
    (f : fixedVectors (awayTranslation R e ι V) K') :
    (awayFormsFixedEquiv R e ι V K' f).1 = f.1.1 :=
  rfl

@[simp]
lemma awayFormsFixedEquiv_symm_apply_coe (K' : Subgroup H') (f : awayLevelForms R e ι V K') :
    ((awayFormsFixedEquiv R e ι V K').symm f).1.1 = f.1 :=
  rfl

end Translation

section Hecke

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) (V : Type t)
  [AddCommGroup V] [Module R V]

/-- The double-coset operator `[K g L]` from forms of level `e⁻¹ (1 × L)` to forms of level
`e⁻¹ (1 × K)`: the published `LevelHecke.heckeOperator` of `awayTranslation`, through
`awayFormsFixedEquiv`. -/
def awayHecke (K L : CompactOpenLevel H') (g : H') :
    awayLevelForms R e ι V L.subgroup →ₗ[R] awayLevelForms R e ι V K.subgroup :=
  (awayFormsFixedEquiv R e ι V K.subgroup).toLinearMap ∘ₗ
    LevelHecke.heckeOperator (awayTranslation R e ι V) K L g ∘ₗ
      (awayFormsFixedEquiv R e ι V L.subgroup).symm.toLinearMap

/-- The formula `([K g L] f) x = ∑ f (x * e⁻¹ (1, k g))` over representatives `k` of
`K / (K ∩ g L g⁻¹)`. -/
lemma awayHecke_apply_coe (K L : CompactOpenLevel H') (g : H')
    (f : awayLevelForms R e ι V L.subgroup) (x : G) :
    (awayHecke R e ι V K L g f).1 x =
      ∑ q : HeckeCosets K L g, f.1 (x * awayHom e ((q.out : H') * g)) := by
  change (LevelHecke.heckeOperator (awayTranslation R e ι V) K L g
    ((awayFormsFixedEquiv R e ι V L.subgroup).symm f) : awayLevelForms R e ι V ⊥).1 x = _
  rw [heckeOperator_apply_out, Submodule.coe_sum, Finset.sum_apply]
  rfl

/-- The double-coset operator commutes with right translation by the first factor `H`. -/
def awayHeckeIntertwining (K L : CompactOpenLevel H') (g : H') :
    (factorTranslation R e ι V L.subgroup).IntertwiningMap
      (factorTranslation R e ι V K.subgroup) where
  toLinearMap := awayHecke R e ι V K L g
  isIntertwining' h := LinearMap.ext fun f =>
    congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (LinearMap.congr_fun (fixedVectorsMap_heckeOperator K L g
        (factorTranslationIntertwining R e ι V h))
        ((awayFormsFixedEquiv R e ι V L.subgroup).symm f)).symm

/-- The double-coset operator `[K g L]` as a morphism of representations of `H` between the
values of `factorFormsPresheaf` at `L` and at `K`. -/
def factorHeckeHom (K L : CompactOpenLevel H') (g : H') :
    (factorFormsPresheaf R e ι V).obj (op L) ⟶ (factorFormsPresheaf R e ι V).obj (op K) :=
  Rep.ofHom (awayHeckeIntertwining R e ι V K L g)

/-- If `g⁻¹ K g ⊆ L`, the operator `[K g L]` is right translation by `g`. -/
lemma awayHecke_eq_awayTranslate {K L : CompactOpenLevel H'} {g : H'}
    (hg : ∀ k ∈ K.subgroup, g⁻¹ * k * g ∈ L.subgroup) :
    awayHecke R e ι V K L g = awayTranslate R e ι V g hg := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change ((LevelHecke.heckeOperator (awayTranslation R e ι V) K L g
    ((awayFormsFixedEquiv R e ι V L.subgroup).symm f) : awayLevelForms R e ι V ⊥) : G → V) = _
  rw [heckeOperator_eq_comp_translateFixed, LinearMap.comp_apply,
    heckeOperator_one_of_le _ (fun k hk => mem_conjLevel.mpr (hg k hk)),
    translateFixed_apply_coe]
  rfl

/-- The map of `factorFormsPresheaf` along an arrow `a : K ⟶ L` of levels is the double-coset
operator `[K a L]` of its element. -/
lemma factorFormsPresheaf_map_eq {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorFormsPresheaf R e ι V).map a.op = factorHeckeHom R e ι V K L a.element := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  exact (LinearMap.congr_fun (awayHecke_eq_awayTranslate R e ι V a.respects) f).symm

/-- The operator `[K 1 K]` is the identity. -/
lemma factorHeckeHom_self (K : CompactOpenLevel H') :
    factorHeckeHom R e ι V K K 1 = 𝟙 _ := by
  have h := factorFormsPresheaf_map_eq R e ι V (𝟙 K)
  rw [op_id, CategoryTheory.Functor.map_id] at h
  exact h.symm

/-- The action `a • f` of an element `a` of the Hecke algebra of `K` on the forms of level
`e⁻¹ (1 × K)`: the published `LevelHecke.heckeAct` of `awayTranslation`, through
`awayFormsFixedEquiv`. -/
def awayHeckeAct (K : CompactOpenLevel H') (a : LevelHeckeAlgebra R K.subgroup) :
    awayLevelForms R e ι V K.subgroup →ₗ[R] awayLevelForms R e ι V K.subgroup :=
  (awayFormsFixedEquiv R e ι V K.subgroup).toLinearMap ∘ₗ
    heckeAct (awayTranslation R e ι V) K.subgroup K.subgroup a ∘ₗ
      (awayFormsFixedEquiv R e ι V K.subgroup).symm.toLinearMap

/-- The action of the Hecke algebra commutes with right translation by the first factor `H`. -/
def awayHeckeActIntertwining (K : CompactOpenLevel H') (a : LevelHeckeAlgebra R K.subgroup) :
    (factorTranslation R e ι V K.subgroup).IntertwiningMap
      (factorTranslation R e ι V K.subgroup) where
  toLinearMap := awayHeckeAct R e ι V K a
  isIntertwining' h := LinearMap.ext fun f =>
    congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (fixedVectorsMap_heckeAct (factorTranslationIntertwining R e ι V h) K.subgroup K.subgroup a
        ((awayFormsFixedEquiv R e ι V K.subgroup).symm f)).symm

/-- The Hecke algebra of `K` acting on the value of `factorFormsPresheaf` at `K`, as a ring
homomorphism to its endomorphisms as a representation of `H`. -/
def formsHeckeAlgebraHom (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorFormsPresheaf R e ι V).obj (op K)) where
  toFun a := Rep.ofHom (awayHeckeActIntertwining R e ι V K a)
  map_one' := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (one_smul (LevelHeckeAlgebra R K.subgroup) ((awayFormsFixedEquiv R e ι V K.subgroup).symm f))
  map_mul' a b := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (mul_smul a b ((awayFormsFixedEquiv R e ι V K.subgroup).symm f))
  map_zero' := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (zero_smul (LevelHeckeAlgebra R K.subgroup) ((awayFormsFixedEquiv R e ι V K.subgroup).symm f))
  map_add' a b := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
      (add_smul a b ((awayFormsFixedEquiv R e ι V K.subgroup).symm f))

/-- The element `[K g K]` of the Hecke algebra acts by the double-coset operator. -/
lemma formsHeckeAlgebraHom_doubleCoset (K : CompactOpenLevel H') (g : H') :
    formsHeckeAlgebraHom R e ι V K (doubleCoset K g) = factorHeckeHom R e ι V K K g := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  exact congrArg (awayFormsFixedEquiv R e ι V K.subgroup)
    (doubleCoset_smul (awayTranslation R e ι V) K g
      ((awayFormsFixedEquiv R e ι V K.subgroup).symm f))

end Hecke

section HeckeSmooth

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  (V : Type t) [AddCommGroup V] [Module R V]

/-- The double-coset operator `[K g L]` on the smooth parts: a morphism of smooth
representations of `H` between the values of `factorSmoothPresheaf` at `L` and at `K`. -/
def factorSmoothHeckeHom (K L : CompactOpenLevel H') (g : H') :
    (factorSmoothPresheaf R e ι V).obj (op L) ⟶ (factorSmoothPresheaf R e ι V).obj (op K) :=
  (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map (factorHeckeHom R e ι V K L g)

/-- The map of `factorSmoothPresheaf` along an arrow `a : K ⟶ L` of levels is the double-coset
operator `[K a L]` of its element. -/
lemma factorSmoothPresheaf_map_eq {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorSmoothPresheaf R e ι V).map a.op = factorSmoothHeckeHom R e ι V K L a.element := by
  change (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map
    ((factorFormsPresheaf R e ι V).map a.op) = _
  rw [factorFormsPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on the value of `factorSmoothPresheaf` at `K`, as a ring
homomorphism to its endomorphisms as a smooth representation of `H`. -/
def smoothHeckeAlgebraHom (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorSmoothPresheaf R e ι V).obj (op K)) :=
  (endRingHom (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H) _).comp
    (formsHeckeAlgebraHom R e ι V K)

/-- The element `[K g K]` of the Hecke algebra acts by the double-coset operator. -/
lemma smoothHeckeAlgebraHom_doubleCoset (K : CompactOpenLevel H') (g : H') :
    smoothHeckeAlgebraHom R e ι V K (doubleCoset K g) = factorSmoothHeckeHom R e ι V K K g := by
  change (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map
    (formsHeckeAlgebraHom R e ι V K (doubleCoset K g)) = _
  rw [formsHeckeAlgebraHom_doubleCoset]
  rfl

end HeckeSmooth

section HeckeExt

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  (V : Type u) [AddCommGroup V] [Module R V]

/-- The functor `Ext^i(W, -)` is additive. -/
instance (W : SmoothRep.{u, u, u} R H) (i : ℕ) : (SmoothExt.ext R H W i).Additive :=
  inferInstanceAs ((SmoothHomComplex.homFunctor R H W).rightDerived i).Additive

/-- The double-coset operator `[K g L]` on `Ext^i(W, -)` of the smooth forms: the map from the
value of `factorExtPresheaf W i` at `L` to its value at `K`. -/
def factorExtHecke (W : SmoothRep.{u, u, u} R H) (i : ℕ) (K L : CompactOpenLevel H') (g : H') :
    (factorExtPresheaf R e ι V W i).obj (op L) ⟶ (factorExtPresheaf R e ι V W i).obj (op K) :=
  (SmoothExt.ext R H W i).map (factorSmoothHeckeHom R e ι V K L g)

/-- The map of `factorExtPresheaf W i` along an arrow `a : K ⟶ L` of levels is the double-coset
operator `[K a L]` of its element. -/
lemma factorExtPresheaf_map_eq (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorExtPresheaf R e ι V W i).map a.op = factorExtHecke R e ι V W i K L a.element := by
  change (SmoothExt.ext R H W i).map ((factorSmoothPresheaf R e ι V).map a.op) = _
  rw [factorSmoothPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on `Ext^i(W, -)` of the smooth forms of level
`e⁻¹ (1 × K)`, as a ring homomorphism to the `R`-linear endomorphisms. -/
def extHeckeAlgebraHom (W : SmoothRep.{u, u, u} R H) (i : ℕ) (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorExtPresheaf R e ι V W i).obj (op K)) :=
  (endRingHom (SmoothExt.ext R H W i) _).comp (smoothHeckeAlgebraHom R e ι V K)

/-- The element `[K g K]` of the Hecke algebra acts on `Ext^i` by the double-coset operator. -/
lemma extHeckeAlgebraHom_doubleCoset (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    (K : CompactOpenLevel H') (g : H') :
    extHeckeAlgebraHom R e ι V W i K (doubleCoset K g) = factorExtHecke R e ι V W i K K g := by
  change (SmoothExt.ext R H W i).map (smoothHeckeAlgebraHom R e ι V K (doubleCoset K g)) = _
  rw [smoothHeckeAlgebraHom_doubleCoset]
  rfl

end HeckeExt

end Langlands.Shimura.EquivariantForms

namespace Langlands.Cohomology.HyperextAbutment

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The map `F^p(K, B) →+ F^p(K, B')` of postcomposition with `ψ⟦n⟧'` is additive in `ψ`. -/
lemma filtrationPostcomp_add (K : C) {B B' : C} (ψ ψ' : B ⟶ B') (n p : ℤ) :
    filtrationPostcomp t K (ψ + ψ') n p =
      filtrationPostcomp t K ψ n p + filtrationPostcomp t K ψ' n p := by
  ext f
  change (f : ShiftedHom K B n) ≫ (ψ + ψ')⟦n⟧' =
    (f : ShiftedHom K B n) ≫ ψ⟦n⟧' + (f : ShiftedHom K B n) ≫ ψ'⟦n⟧'
  rw [CategoryTheory.Functor.map_add, Preadditive.comp_add]

/-- The map `gr^p(K, B) →+ gr^p(K, B')` of postcomposition with `ψ⟦n⟧'` is additive in `ψ`. -/
lemma gradedPostcomp_add (K : C) {B B' : C} (ψ ψ' : B ⟶ B') (n p : ℤ) :
    gradedPostcomp t K (ψ + ψ') n p = gradedPostcomp t K ψ n p + gradedPostcomp t K ψ' n p := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun f => ?_)
  change (QuotientAddGroup.mk (filtrationPostcomp t K (ψ + ψ') n p f) : graded t K B' n p) =
    QuotientAddGroup.mk (filtrationPostcomp t K ψ n p f) +
      QuotientAddGroup.mk (filtrationPostcomp t K ψ' n p f)
  rw [filtrationPostcomp_add, AddMonoidHom.add_apply, QuotientAddGroup.mk_add]

/-- The functor `B ↦ F^p(K, B)` is additive. -/
instance filtrationFunctor_additive (K : C) (n p : ℤ) : (filtrationFunctor t K n p).Additive where
  map_add {_ _ ψ ψ'} := AddCommGrpCat.hom_ext (filtrationPostcomp_add t K ψ ψ' n p)

/-- The functor `B ↦ gr^p(K, B)` is additive. -/
instance gradedFunctor_additive (K : C) (n p : ℤ) : (gradedFunctor t K n p).Additive where
  map_add {_ _ ψ ψ'} := AddCommGrpCat.hom_ext (gradedPostcomp_add t K ψ ψ' n p)

end Langlands.Cohomology.HyperextAbutment

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel Langlands.Shimura.LevelHecke

universe u uΓ uH' w

section HeckeAbutment

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  (V : Type u) [AddCommGroup V] [Module R V] [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R H)]

/-- The double-coset operator `[K g L]` on the abutment `Hom(X, A(-)[n])`, by postcomposition. -/
def factorAbutmentHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (K L : CompactOpenLevel H') (g : H') :
    (factorAbutmentPresheaf R e ι V X n).obj (op L) ⟶
      (factorAbutmentPresheaf R e ι V X n).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map (factorSmoothHeckeHom R e ι V K L g)

/-- The map of `factorAbutmentPresheaf X n` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma factorAbutmentPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorAbutmentPresheaf R e ι V X n).map a.op =
      factorAbutmentHecke R e ι V X n K L a.element := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map ((factorSmoothPresheaf R e ι V).map a.op) = _
  rw [factorSmoothPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on the abutment `Hom(X, A(K)[n])` by postcomposition, as a
ring homomorphism to its additive endomorphisms. -/
def abutmentHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorAbutmentPresheaf R e ι V X n).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)) _).comp (smoothHeckeAlgebraHom R e ι V K)

/-- The element `[K g K]` of the Hecke algebra acts on the abutment by the double-coset
operator. -/
lemma abutmentHeckeAlgebraHom_doubleCoset (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n : ℤ) (K : CompactOpenLevel H') (g : H') :
    abutmentHeckeAlgebraHom R e ι V X n K (doubleCoset K g) =
      factorAbutmentHecke R e ι V X n K K g := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map (smoothHeckeAlgebraHom R e ι V K (doubleCoset K g)) = _
  rw [smoothHeckeAlgebraHom_doubleCoset]
  rfl

/-- The double-coset operator `[K g L]` on the step `F^p` of the abutment filtration, by
postcomposition. -/
def factorFiltrationHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K L : CompactOpenLevel H') (g : H') :
    (factorFiltrationPresheaf R e ι V X n p).obj (op L) ⟶
      (factorFiltrationPresheaf R e ι V X n p).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p).map
      (factorSmoothHeckeHom R e ι V K L g)

/-- The map of `factorFiltrationPresheaf X n p` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma factorFiltrationPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorFiltrationPresheaf R e ι V X n p).map a.op =
      factorFiltrationHecke R e ι V X n p K L a.element := by
  change AddCommGrpCat.ofHom (HyperextAbutment.filtrationPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((factorSmoothPresheaf R e ι V).map a.op)) n p) = _
  rw [factorSmoothPresheaf_map_eq]
  rfl

/-- The inclusion `F^p ⊆ Hom(X, A(-)[n])` commutes with the double-coset operators. -/
lemma factorFiltrationHecke_comp_filtrationι (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (K L : CompactOpenLevel H') (g : H') :
    factorFiltrationHecke R e ι V X n p K L g ≫
        (HyperextAbutment.filtrationι TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op K))) =
      (HyperextAbutment.filtrationι TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op L))) ≫
        factorAbutmentHecke R e ι V X n K L g :=
  (HyperextAbutment.filtrationι TStructure.t X n p).naturality _

/-- The Hecke algebra of `K` acting on the step `F^p` of the abutment filtration on
`Hom(X, A(K)[n])`, as a ring homomorphism to its additive endomorphisms. -/
def filtrationHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorFiltrationPresheaf R e ι V X n p).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p) _).comp
      (smoothHeckeAlgebraHom R e ι V K)

/-- The double-coset operator `[K g L]` on the graded piece `gr^p` of the abutment filtration, by
postcomposition. -/
def factorGradedHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K L : CompactOpenLevel H') (g : H') :
    (factorGradedPresheaf R e ι V X n p).obj (op L) ⟶
      (factorGradedPresheaf R e ι V X n p).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p).map
      (factorSmoothHeckeHom R e ι V K L g)

/-- The map of `factorGradedPresheaf X n p` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma factorGradedPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) {K L : CompactOpenLevel H'} (a : K ⟶ L) :
    (factorGradedPresheaf R e ι V X n p).map a.op =
      factorGradedHecke R e ι V X n p K L a.element := by
  change AddCommGrpCat.ofHom (HyperextAbutment.gradedPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((factorSmoothPresheaf R e ι V).map a.op)) n p) = _
  rw [factorSmoothPresheaf_map_eq]
  rfl

/-- The projection `F^p ⟶ gr^p` commutes with the double-coset operators. -/
lemma factorFiltrationHecke_comp_gradedπ (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (K L : CompactOpenLevel H') (g : H') :
    factorFiltrationHecke R e ι V X n p K L g ≫
        (HyperextAbutment.gradedπ TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op K))) =
      (HyperextAbutment.gradedπ TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op L))) ≫
        factorGradedHecke R e ι V X n p K L g :=
  (HyperextAbutment.gradedπ TStructure.t X n p).naturality _

/-- The Hecke algebra of `K` acting on the graded piece `gr^p` of the abutment filtration on
`Hom(X, A(K)[n])`, as a ring homomorphism to its additive endomorphisms. -/
def gradedHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K : CompactOpenLevel H') :
    LevelHeckeAlgebra R K.subgroup →+* End ((factorGradedPresheaf R e ι V X n p).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p) _).comp
      (smoothHeckeAlgebraHom R e ι V K)

end HeckeAbutment

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.EquivariantForms Langlands.Shimura.LevelHecke

universe u w

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (p : ℕ) (hp : p ≠ 0) (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V] [Module R V]

/-- The double-coset operator `[K g L]` for `g ∈ GJ(A_f^{(p)})` between the values of
`dividingSmoothPresheaf` at `L` and at `K`, as a morphism of smooth representations of
`GJ(∏_{v ∣ p} ℚ_v)`. -/
def dividingSmoothHecke (K L : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.PrimeToPoints p) :
    (dividingSmoothPresheaf σ p hp R V).obj (op L) ⟶
      (dividingSmoothPresheaf σ p hp R V).obj (op K) :=
  factorSmoothHeckeHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V K L g

/-- The map of `dividingSmoothPresheaf` along an arrow `a : K ⟶ L` of levels is the double-coset
operator `[K a L]` of its element. -/
lemma dividingSmoothPresheaf_map_eq {K L : CompactOpenLevel (σ.PrimeToPoints p)} (a : K ⟶ L) :
    (dividingSmoothPresheaf σ p hp R V).map a.op = dividingSmoothHecke σ p hp R V K L a.element :=
  factorSmoothPresheaf_map_eq R _ _ V a

/-- The Hecke algebra of a compact open level `K` of `GJ(A_f^{(p)})` acting on the value of
`dividingSmoothPresheaf` at `K`, as a ring homomorphism to its endomorphisms as a smooth
representation of `GJ(∏_{v ∣ p} ℚ_v)`. -/
def dividingSmoothHeckeAlgebraHom (K : CompactOpenLevel (σ.PrimeToPoints p)) :
    LevelHeckeAlgebra R K.subgroup →+* End ((dividingSmoothPresheaf σ p hp R V).obj (op K)) :=
  smoothHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V K

/-- The double-coset operator `[K g L]` on `Ext^i(W, -)` of the forms of
`dividingSmoothPresheaf`: the map from the value of `dividingExtPresheaf W i` at `L` to its value
at `K`. -/
def dividingExtHecke (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (K L : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.PrimeToPoints p) :
    (dividingExtPresheaf σ p hp R V W i).obj (op L) ⟶
      (dividingExtPresheaf σ p hp R V W i).obj (op K) :=
  factorExtHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V W i K L g

/-- The map of `dividingExtPresheaf W i` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma dividingExtPresheaf_map_eq (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    {K L : CompactOpenLevel (σ.PrimeToPoints p)} (a : K ⟶ L) :
    (dividingExtPresheaf σ p hp R V W i).map a.op =
      dividingExtHecke σ p hp R V W i K L a.element :=
  factorExtPresheaf_map_eq R _ _ V W i a

/-- The Hecke algebra of a compact open level `K` of `GJ(A_f^{(p)})` acting on
`Ext^i(W, -)` of the forms of `dividingSmoothPresheaf` at `K`, as a ring homomorphism to the
`R`-linear endomorphisms. -/
def dividingExtHeckeAlgebraHom (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (K : CompactOpenLevel (σ.PrimeToPoints p)) :
    LevelHeckeAlgebra R K.subgroup →+* End ((dividingExtPresheaf σ p hp R V W i).obj (op K)) :=
  extHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V W i K

/-- The element `[K g K]` of the Hecke algebra acts on `Ext^i` by the double-coset operator. -/
lemma dividingExtHeckeAlgebraHom_doubleCoset (W : SmoothRep.{u, u, u} R (σ.DividingPoints p))
    (i : ℕ) (K : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.PrimeToPoints p) :
    dividingExtHeckeAlgebraHom σ p hp R V W i K (doubleCoset K g) =
      dividingExtHecke σ p hp R V W i K K g :=
  extHeckeAlgebraHom_doubleCoset R _ _ V W i K g

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R (σ.DividingPoints p))]

/-- The double-coset operator `[K g L]` on the abutment `Hom(X, A(-)[n])` of
`dividingSpectralSequence`, by postcomposition. -/
def dividingAbutmentHecke (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (n : ℤ) (K L : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.PrimeToPoints p) :
    (dividingAbutmentPresheaf σ p hp R V X n).obj (op L) ⟶
      (dividingAbutmentPresheaf σ p hp R V X n).obj (op K) :=
  factorAbutmentHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n K L g

/-- The map of `dividingAbutmentPresheaf X n` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma dividingAbutmentPresheaf_map_eq
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    {K L : CompactOpenLevel (σ.PrimeToPoints p)} (a : K ⟶ L) :
    (dividingAbutmentPresheaf σ p hp R V X n).map a.op =
      dividingAbutmentHecke σ p hp R V X n K L a.element :=
  factorAbutmentPresheaf_map_eq R _ _ V X n a

/-- The Hecke algebra of a compact open level `K` of `GJ(A_f^{(p)})` acting on the abutment
`Hom(X, A(K)[n])` by postcomposition. -/
def dividingAbutmentHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (K : CompactOpenLevel (σ.PrimeToPoints p)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingAbutmentPresheaf σ p hp R V X n).obj (op K)) :=
  abutmentHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n K

/-- The Hecke algebra of a compact open level `K` of `GJ(A_f^{(p)})` acting on the step `F^i` of
the abutment filtration on `Hom(X, A(K)[n])`. -/
def dividingFiltrationHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K : CompactOpenLevel (σ.PrimeToPoints p)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingFiltrationPresheaf σ p hp R V X n i).obj (op K)) :=
  filtrationHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n i K

/-- The Hecke algebra of a compact open level `K` of `GJ(A_f^{(p)})` acting on the graded piece
`gr^i` of the abutment filtration on `Hom(X, A(K)[n])`. -/
def dividingGradedHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K : CompactOpenLevel (σ.PrimeToPoints p)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingGradedPresheaf σ p hp R V X n i).obj (op K)) :=
  gradedHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n i K

end Langlands.Shimura.DefiniteForms
