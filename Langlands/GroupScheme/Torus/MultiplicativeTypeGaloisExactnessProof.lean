import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat

/-! # Finite Galois character exactness for groups of multiplicative type: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace MultiplicativeTypeGaloisExactness

/-! ### Character-level algebra -/

section Algebra

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : B →+ A) (g : C →+ B)

/-- The pointwise exactness criterion with values in a commutative group `M`: a
character of `B` kills the image of `g` exactly when it factors through `f`. -/
def PointCriterion (M : Type u) [CommGroup M] : Prop :=
  ∀ χ : Multiplicative B →* M,
    (χ.comp (AddMonoidHom.toMultiplicative g) = 1 ↔
      ∃ ψ : Multiplicative A →* M, ψ.comp (AddMonoidHom.toMultiplicative f) = χ)

/-- A surjective `f` whose kernel is the image of `g` satisfies the criterion. -/
theorem pointCriterion_of_exact (hf : Function.Surjective f) (hfg : Function.Exact g f)
    (M : Type u) [CommGroup M] : PointCriterion f g M := by
  intro χ
  constructor
  · intro hχ
    have hker : ∀ b b' : B, f b = f b' →
        χ (Multiplicative.ofAdd b) = χ (Multiplicative.ofAdd b') := by
      intro b b' hbb
      obtain ⟨c, hc⟩ := (hfg (b - b')).1 (by rw [map_sub, hbb, sub_self])
      have hc' : χ (Multiplicative.ofAdd (g c)) = 1 := by
        simpa using DFunLike.congr_fun hχ (Multiplicative.ofAdd c)
      have hb : b = g c + b' := by rw [hc, sub_add_cancel]
      rw [hb, ofAdd_add, map_mul, hc', one_mul]
    let s := Function.surjInv hf
    refine ⟨MonoidHom.mk' (fun a => χ (Multiplicative.ofAdd (s a.toAdd))) ?_, ?_⟩
    · intro a a'
      rw [← map_mul, ← ofAdd_add]
      apply hker
      rw [map_add, Function.surjInv_eq hf, Function.surjInv_eq hf, Function.surjInv_eq hf,
        toAdd_mul]
    · apply MonoidHom.ext
      intro b
      change χ (Multiplicative.ofAdd (s (f b.toAdd))) = χ b
      exact hker _ _ (Function.surjInv_eq hf _)
  · rintro ⟨ψ, rfl⟩
    apply MonoidHom.ext
    intro c
    change ψ (Multiplicative.ofAdd (f (g c.toAdd))) = 1
    rw [hfg.apply_apply_eq_zero, ofAdd_zero, map_one]

/-- The criterion for two injective universal characters gives exactness. -/
theorem exact_of_pointCriterion (M₁ M₂ : Type u) [CommGroup M₁] [CommGroup M₂]
    (u₁ : Multiplicative A →* M₁) (hu₁ : Function.Injective u₁)
    (u₂ : Multiplicative (B ⧸ g.range) →* M₂) (hu₂ : Function.Injective u₂)
    (h₁ : PointCriterion f g M₁) (h₂ : PointCriterion f g M₂) : Function.Exact g f := by
  intro b
  constructor
  · intro hb
    let χ : Multiplicative B →* M₂ :=
      u₂.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' g.range))
    obtain ⟨ψ, hψ⟩ := (h₂ χ).1 (by
      apply MonoidHom.ext
      intro c
      change u₂ (Multiplicative.ofAdd (QuotientAddGroup.mk' g.range (g c.toAdd))) = 1
      rw [QuotientAddGroup.mk'_apply,
        (QuotientAddGroup.eq_zero_iff (g c.toAdd)).2 (AddMonoidHom.mem_range.2 ⟨c.toAdd, rfl⟩),
        ofAdd_zero, map_one])
    have h := DFunLike.congr_fun hψ (Multiplicative.ofAdd b)
    change ψ (Multiplicative.ofAdd (f b)) =
      u₂ (Multiplicative.ofAdd (QuotientAddGroup.mk' g.range b)) at h
    rw [hb, ofAdd_zero, map_one, eq_comm, ← map_one u₂] at h
    have h' := hu₂ h
    rw [ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h'
    obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 h'
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    have h := (h₁ (u₁.comp (AddMonoidHom.toMultiplicative f))).2 ⟨u₁, rfl⟩
    have h' := DFunLike.congr_fun h (Multiplicative.ofAdd c)
    change u₁ (Multiplicative.ofAdd (f (g c))) = 1 at h'
    rw [← map_one u₁] at h'
    exact ofAdd_eq_one.1 (hu₁ h')

end Algebra

/-! ### Group algebras -/

section GroupAlgebra

variable (K : Type u) [Field K] {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- The group-algebra map along `f` is surjective exactly when `f` is. -/
theorem mapDomainRingHom_surjective_iff (f : B →+ A) :
    Function.Surjective (AddMonoidAlgebra.mapDomainRingHom K f) ↔ Function.Surjective f := by
  constructor
  · intro h a
    by_contra ha
    obtain ⟨x, hx⟩ := h (AddMonoidAlgebra.single a 1)
    have hc := congrArg (fun y : AddMonoidAlgebra K A => y.coeff a) hx
    change Finsupp.mapDomain f x.coeff a = Finsupp.single a (1 : K) a at hc
    rw [Finsupp.mapDomain_of_notMem_range _ _ ha, Finsupp.single_eq_same] at hc
    exact zero_ne_one hc
  · intro hf x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | single a r =>
      obtain ⟨b, rfl⟩ := hf a
      exact ⟨AddMonoidAlgebra.single b r, by
        rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]⟩

/-- An injective group-algebra map along `g` forces `g` to be injective. -/
theorem injective_of_mapDomainRingHom (g : B →+ A)
    (h : Function.Injective (AddMonoidAlgebra.mapDomainRingHom K g)) :
    Function.Injective g := by
  intro c c' hc
  apply AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K))
  apply h
  change AddMonoidAlgebra.mapDomainRingHom K g (AddMonoidAlgebra.single c 1) =
    AddMonoidAlgebra.mapDomainRingHom K g (AddMonoidAlgebra.single c' 1)
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single, hc]

/-- Between finitely generated character groups, the group-algebra map is of finite
presentation. -/
theorem mapDomainRingHom_finitePresentation [AddGroup.FG A] [AddGroup.FG B] (g : B →+ A) :
    (AddMonoidAlgebra.mapDomainRingHom K g).FinitePresentation := by
  apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap K (AddMonoidAlgebra K B))
  · have hcomp : (AddMonoidAlgebra.mapDomainRingHom K g).comp
        (algebraMap K (AddMonoidAlgebra K B)) = algebraMap K (AddMonoidAlgebra K A) := by
      apply RingHom.ext
      intro r
      rw [RingHom.comp_apply, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coe_algebraMap,
        Function.comp_apply, Function.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single, map_zero]
    rw [hcomp, RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  · rw [RingHom.finiteType_algebraMap]
    infer_instance

end GroupAlgebra

/-! ### Diagonalizable restriction maps -/

section Split

variable (K : Type u) [Field K] {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

/-- `D(A) → D(B)` is a closed subgroup exactly when `f : B →+ A` is surjective. -/
theorem isClosedSubgroup_restrictMap_iff (f : B →+ A) :
    IsClosedSubgroup (Diagonalizable.restrictMap (CommRingCat.of K) f) ↔
      Function.Surjective f := by
  rw [← mapDomainRingHom_surjective_iff K f]
  change IsClosedImmersion (Diagonalizable.restrictMap (CommRingCat.of K) f).hom.hom.left ↔ _
  rw [Diagonalizable.restrictMap_left]
  constructor
  · intro h
    have := h
    exact CentralExtensionHopfSpec.surjective_of_isClosedImmersion
      (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom K f))
  · intro h
    exact IsClosedImmersion.spec_of_surjective _ h

/-- `D(B) → D(C)` is flat and surjective exactly when `g : C →+ B` is injective. -/
theorem flat_surjective_restrictMap_iff (g : C →+ B) :
    (Flat (Diagonalizable.restrictMap (CommRingCat.of K) g).hom.hom.left ∧
      Surjective (Diagonalizable.restrictMap (CommRingCat.of K) g).hom.hom.left) ↔
      Function.Injective g := by
  constructor
  · intro h
    rw [Diagonalizable.restrictMap_left, flat_and_surjective_SpecMap_iff] at h
    exact injective_of_mapDomainRingHom K g h.injective
  · exact Diagonalizable.flat_and_surjective_restrictMap (CommRingCat.of K) g

/-- Between finitely generated groups, `D(B) → D(C)` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_restrictMap [AddGroup.FG B] [AddGroup.FG C]
    (g : C →+ B) :
    LocallyOfFinitePresentation (Diagonalizable.restrictMap (CommRingCat.of K) g).hom.hom.left := by
  rw [Diagonalizable.restrictMap_left, LocallyOfFinitePresentation.SpecMap_iff]
  exact mapDomainRingHom_finitePresentation K g

/-- On points, `D(B) → D(C)` restricts characters along `g`. -/
theorem characterPointsEquiv_restrictMap (g : C →+ B) (U : Over (Spec (CommRingCat.of K)))
    (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of K) B).X) :
    Diagonalizable.characterPointsEquiv (CommRingCat.of K) C U
        (x ≫ (Diagonalizable.restrictMap (CommRingCat.of K) g).hom.hom) =
      (Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U x).comp
        (AddMonoidHom.toMultiplicative g) := by
  apply MonoidHom.ext
  intro c
  exact Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of K) g x c.toAdd

/-- A point of `D(B)` is killed by `D(B) → D(C)` exactly when its character kills the
image of `g`. -/
theorem comp_restrictMap_eq_one_iff (g : C →+ B) {U : Over (Spec (CommRingCat.of K))}
    (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of K) B).X) :
    x ≫ (Diagonalizable.restrictMap (CommRingCat.of K) g).hom.hom = 1 ↔
      (Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U x).comp
        (AddMonoidHom.toMultiplicative g) = 1 := by
  rw [← characterPointsEquiv_restrictMap]
  constructor
  · intro h
    rw [h]
    exact map_one _
  · intro h
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of K) C U).injective
    rw [h]
    exact (map_one _).symm

/-- A point of `D(B)` lies in the range of `D(A) → D(B)` exactly when its character
factors through `f`. -/
theorem mem_range_restrictMap_iff (f : B →+ A) {U : Over (Spec (CommRingCat.of K))}
    (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of K) B).X) :
    x ∈ (SubgroupFunctor.range (Diagonalizable.restrictMap (CommRingCat.of K) f)).carrier U ↔
      ∃ ψ : Multiplicative A →* (Γ(U.left, ⊤))ˣ,
        ψ.comp (AddMonoidHom.toMultiplicative f) =
          Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U x := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (characterPointsEquiv_restrictMap K f U y).symm⟩
  · rintro ⟨ψ, hψ⟩
    refine ⟨(Diagonalizable.characterPointsEquiv (CommRingCat.of K) A U).symm ψ, ?_⟩
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U).injective
    rw [characterPointsEquiv_restrictMap, MulEquiv.apply_symm_apply, hψ]

/-- The actual kernel of `D(B) → D(C)` has the range of `D(A) → D(B)` on every test exactly
when the pointwise criterion holds for the units of every test. -/
theorem range_kernelι_eq_range_iff (f : B →+ A) (g : C →+ B) :
    SubgroupFunctor.range (kernelι (Diagonalizable.restrictMap (CommRingCat.of K) g)) =
        SubgroupFunctor.range (Diagonalizable.restrictMap (CommRingCat.of K) f) ↔
      ∀ U : Over (Spec (CommRingCat.of K)), PointCriterion f g (Γ(U.left, ⊤))ˣ := by
  constructor
  · intro h U χ
    let x := (Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U).symm χ
    have hx : Diagonalizable.characterPointsEquiv (CommRingCat.of K) B U x = χ :=
      MulEquiv.apply_symm_apply _ _
    have h₁ := mem_range_kernelι_iff (Diagonalizable.restrictMap (CommRingCat.of K) g) x
    rw [comp_restrictMap_eq_one_iff, hx, h, mem_range_restrictMap_iff, hx] at h₁
    exact h₁.symm
  · intro h
    apply SubgroupFunctor.ext
    intro U
    ext x
    rw [mem_range_kernelι_iff, comp_restrictMap_eq_one_iff, mem_range_restrictMap_iff]
    exact h U _

/-- Over a field, the universal character of `D(Λ)` is injective. -/
theorem characterPointsEquiv_id_injective (Λ : Type u) [AddCommGroup Λ] :
    Function.Injective (Diagonalizable.characterPointsEquiv (CommRingCat.of K) Λ _
      (𝟙 (Diagonalizable.groupScheme (CommRingCat.of K) Λ).X)) := by
  intro m m' h
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective m
  obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective m'
  have e := congrArg Units.val h
  rw [DiagonalizableCharacter.characterPointsEquiv_val,
    DiagonalizableCharacter.characterPointsEquiv_val,
    DiagonalizableCharacter.lift_characterPointsEquiv_id] at e
  have ei := congrArg (DiagonalizableCharacter.sectionsIso (CommRingCat.of K) Λ).hom.hom e
  have h₁ := ConcreteCategory.congr_hom
    (DiagonalizableCharacter.sectionsIso (CommRingCat.of K) Λ).inv_hom_id
    (AddMonoidAlgebra.single a (1 : K))
  have h₂ := ConcreteCategory.congr_hom
    (DiagonalizableCharacter.sectionsIso (CommRingCat.of K) Λ).inv_hom_id
    (AddMonoidAlgebra.single a' (1 : K))
  exact congrArg Multiplicative.ofAdd
    (AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K))
      (h₁.symm.trans (ei.trans h₂)))

/-- **Split core.** For finitely generated `B` and `C`, the diagonalizable maps
`D(A) → D(B) → D(C)` form a closed subgroup with its fppf quotient exactly when
`0 → C → B → A → 0` is exact. -/
theorem splitCore [AddGroup.FG B] [AddGroup.FG C] (f : B →+ A) (g : C →+ B) :
    (IsClosedSubgroup (Diagonalizable.restrictMap (CommRingCat.of K) f) ∧
      RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range (Diagonalizable.restrictMap (CommRingCat.of K) f))
        (Diagonalizable.restrictMap (CommRingCat.of K) g)) ↔
      (Function.Injective g ∧ Function.Exact g f ∧ Function.Surjective f) := by
  constructor
  · rintro ⟨hc, hflat, hsurj, -, hker⟩
    have hP := (range_kernelι_eq_range_iff K f g).1 hker
    refine ⟨(flat_surjective_restrictMap_iff K g).1 ⟨hflat, hsurj⟩, ?_,
      (isClosedSubgroup_restrictMap_iff K f).1 hc⟩
    exact exact_of_pointCriterion f g _ _ _ (characterPointsEquiv_id_injective K A) _
      (characterPointsEquiv_id_injective K (B ⧸ g.range)) (hP _) (hP _)
  · rintro ⟨hg, hfg, hf⟩
    have hfs := (flat_surjective_restrictMap_iff K g).2 hg
    exact ⟨(isClosedSubgroup_restrictMap_iff K f).2 hf, hfs.1, hfs.2,
      locallyOfFinitePresentation_restrictMap K g,
      (range_kernelι_eq_range_iff K f g).2 fun U => pointCriterion_of_exact f g hf hfg _⟩

end Split

/-! ### Transport along isomorphisms -/

section Transport

variable {S : Scheme.{u}} {N N' E E' Q Q' : GroupScheme S}

/-- The range of `j ≫ b.hom` is the preimage of the range of `j` under `b.inv`. -/
theorem range_comp_iso_hom (j : N ⟶ E) (b : E ≅ E') :
    SubgroupFunctor.range (j ≫ b.hom) = (SubgroupFunctor.range j).comap b.inv := by
  ext T x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom b.hom b.inv,
      b.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom,
      b.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- A closed subgroup with its fppf quotient transports along isomorphisms of all three
groups. -/
theorem transport (a : N ≅ N') (b : E ≅ E') (c : Q ≅ Q') {j : N ⟶ E} {r : E ⟶ Q}
    (h : IsClosedSubgroup j ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) r) :
    IsClosedSubgroup (a.inv ≫ j ≫ b.hom) ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (a.inv ≫ j ≫ b.hom))
        (b.inv ≫ r ≫ c.hom) := by
  obtain ⟨hj, hr⟩ := h
  refine ⟨IsClosedSubgroup.iso_comp a.symm (hj.comp_iso b), ?_⟩
  rw [show SubgroupFunctor.range (a.inv ≫ j ≫ b.hom) = SubgroupFunctor.range (j ≫ b.hom) from
    SubgroupFunctor.range_iso_comp a.symm _, range_comp_iso_hom]
  exact (hr.comp_iso c).comapIso b

/-- The transport is an equivalence. -/
theorem transport_iff (a : N ≅ N') (b : E ≅ E') (c : Q ≅ Q') (j : N ⟶ E) (r : E ⟶ Q)
    {j' : N' ⟶ E'} {r' : E' ⟶ Q'} (hj : a.inv ≫ j ≫ b.hom = j')
    (hr : b.inv ≫ r ≫ c.hom = r') :
    (IsClosedSubgroup j' ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j') r') ↔
      (IsClosedSubgroup j ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) r) := by
  subst hj hr
  constructor
  · intro h
    have h' := transport a.symm b.symm c.symm h
    simpa using h'
  · exact transport a b c

end Transport

/-! ### Descent along an fpqc base change -/

section Descent

variable {B S : Scheme.{u}} (p : S ⟶ B) [Flat p] [Surjective p] [QuasiCompact p]
  {N G R : GroupScheme B}

/-- Over an fpqc base change, a closed subgroup with its fppf quotient descends, and
conversely. -/
theorem descent_iff (i : N ⟶ G) (r : G ⟶ R) :
    (IsClosedSubgroup ((GroupScheme.baseChange p).map i) ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange p).map i))
        ((GroupScheme.baseChange p).map r)) ↔
      (IsClosedSubgroup i ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r) := by
  constructor
  · rintro ⟨hi, hq⟩
    have hp := baseChange_map_isPullback p i
    have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (pullback.fst G.X.hom p) :=
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    have hci : IsClosedSubgroup i :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion) hp hfpqc hi
    refine ⟨hci, ?_⟩
    have : IsClosedImmersion i.hom.hom.left := hci
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    exact RelativeRoot.IsFppfQuotient.of_baseChange_iso p i r _ (Iso.refl _)
      (Category.comp_id _) hq
  · rintro ⟨hi, hq⟩
    refine ⟨hi.baseChange p, ?_⟩
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange p

end Descent

/-! ### Evaluation characters -/

section Characters

variable (K : Type u) [Field K] {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- The homomorphism `D(A) ⟶ D(B)` of commutative group schemes attached to `f : B →+ A`. -/
abbrev restrictHom (f : B →+ A) :
    Diagonalizable.groupScheme (CommRingCat.of K) A ⟶
      Diagonalizable.groupScheme (CommRingCat.of K) B :=
  Additive.ofMul (Diagonalizable.restrictMap (CommRingCat.of K) f)

/-- Pulling back the evaluation character at `m` along `D(f)` evaluates at `f m`. -/
theorem restrictHom_comp_evalCharacter (f : B →+ A) (m : B) :
    restrictHom K f ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of K) B m =
      DiagonalizableCharacter.evalCharacter (CommRingCat.of K) A (f m) := by
  apply characterLattice.ext_points
  intro U x
  rw [comp_groupHom_comp, DiagonalizableCharacter.evalCharacter_apply,
    DiagonalizableCharacter.evalCharacter_apply]
  exact Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of K) f x m

/-- The isomorphism of underlying group schemes of an isomorphism of commutative group
schemes. -/
def grpIso {S : Scheme.{u}} {G H : CommGroupScheme S} (e : G ≅ H) : G.toGrp ≅ H.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id

end Characters

end MultiplicativeTypeGaloisExactness

open MultiplicativeTypeGaloisExactness in
/-- **Finite Galois character exactness for groups of multiplicative type.** Over a
common finite Galois splitting field, a closed subgroup `i` with fppf quotient `q`
corresponds exactly to a short exact, Galois-equivariant sequence of actual character
lattices. -/
theorem multiplicativeTypeGaloisExactness : MultiplicativeTypeGaloisExactnessStatement.{u} := by
  intro k L _ _ _ _ _ N E Q M_N M_E M_Q _ _ _ _ _ _ eN eE eQ i q BC pullQ pullN
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k L
  -- The base-changed maps are restriction maps of the models.
  obtain ⟨f, hf⟩ := (DiagonalizableCharacter.restrictMap_bijective L M_N M_E).2
    (CommGroupScheme.groupHom (eN.inv ≫ BC.map i ≫ eE.hom))
  obtain ⟨g, hg⟩ := (DiagonalizableCharacter.restrictMap_bijective L M_E M_Q).2
    (CommGroupScheme.groupHom (eE.inv ≫ BC.map q ≫ eQ.hom))
  beta_reduce at hf hg
  have hj : (grpIso eN).inv ≫ (GroupScheme.baseChange (algebraBaseMap k L)).map
      (CommGroupScheme.groupHom i) ≫ (grpIso eE).hom =
      Diagonalizable.restrictMap (CommRingCat.of L) f := hf.symm
  have hr : (grpIso eE).inv ≫ (GroupScheme.baseChange (algebraBaseMap k L)).map
      (CommGroupScheme.groupHom q) ≫ (grpIso eQ).hom =
      Diagonalizable.restrictMap (CommRingCat.of L) g := hg.symm
  have key := (descent_iff (algebraBaseMap k L) (CommGroupScheme.groupHom i)
      (CommGroupScheme.groupHom q)).symm.trans
    ((transport_iff (grpIso eN) (grpIso eE) (grpIso eQ) _ _ hj hr).symm.trans
      (splitCore L f g))
  refine key.trans ?_
  -- Characters of the models are evaluation characters.
  let ΦN := (DiagonalizableCharacter.evalCharacterEquiv L M_N).trans
    (characterLattice.congr eN).symm
  let ΦE := (DiagonalizableCharacter.evalCharacterEquiv L M_E).trans
    (characterLattice.congr eE).symm
  let ΦQ := (DiagonalizableCharacter.evalCharacterEquiv L M_Q).trans
    (characterLattice.congr eQ).symm
  have hF : restrictHom L f = eN.inv ≫ BC.map i ≫ eE.hom := congrArg Additive.ofMul hf
  have hG : restrictHom L g = eE.inv ≫ BC.map q ≫ eQ.hom := congrArg Additive.ofMul hg
  have ladderN : ∀ m : M_E, pullN (ΦE m) = ΦN (f m) := by
    intro m
    change BC.map i ≫ eE.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of L) M_E m =
      eN.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of L) M_N (f m)
    rw [← restrictHom_comp_evalCharacter L f m, hF]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have ladderQ : ∀ m : M_Q, pullQ (ΦQ m) = ΦE (g m) := by
    intro m
    change BC.map q ≫ eQ.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of L) M_Q m =
      eE.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of L) M_E (g m)
    rw [← restrictHom_comp_evalCharacter L g m, hG]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let PQ : characterLattice (BC.obj Q) →+ characterLattice (BC.obj E) :=
    Preadditive.leftComp _ (BC.map q)
  let PN : characterLattice (BC.obj E) →+ characterLattice (BC.obj N) :=
    Preadditive.leftComp _ (BC.map i)
  have hex : Function.Exact pullQ pullN ↔ Function.Exact g f :=
    Function.Exact.iff_of_ladder_addEquiv ΦQ ΦE ΦN (f₁₂ := g) (f₂₃ := f) (g₁₂ := PQ)
      (g₂₃ := PN) (AddMonoidHom.ext ladderQ) (AddMonoidHom.ext ladderN)
  have hinj : Function.Injective pullQ ↔ Function.Injective g := by
    have h : pullQ ∘ ΦQ = ΦE ∘ g := funext ladderQ
    rw [← EquivLike.injective_comp ΦQ pullQ, h, EquivLike.comp_injective]
  have hsur : Function.Surjective pullN ↔ Function.Surjective f := by
    have h : pullN ∘ ΦE = ΦN ∘ f := funext ladderN
    rw [← EquivLike.surjective_comp ΦE pullN, h, EquivLike.comp_surjective]
  -- Equivariance is naturality of the canonical Galois actions.
  have eqQ : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (BC.obj Q)),
      pullQ (characterLattice.galoisRepresentation k L Q σ χ) =
        characterLattice.galoisRepresentation k L E σ (pullQ χ) :=
    fun σ χ => (characterLattice.galoisRepresentation_naturality k L q σ χ).symm
  have eqN : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (BC.obj E)),
      pullN (characterLattice.galoisRepresentation k L E σ χ) =
        characterLattice.galoisRepresentation k L N σ (pullN χ) :=
    fun σ χ => (characterLattice.galoisRepresentation_naturality k L i σ χ).symm
  rw [hinj, hex, hsur]
  exact ⟨fun h => ⟨eqQ, eqN, h⟩, fun h => h.2.2⟩

end Langlands.GroupScheme
