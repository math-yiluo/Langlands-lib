import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentrality
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.SplitUnipotentStableCenter
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Commutator

/-! # The preimage of a central subgroup of multiplicative type is central

Let `G` be a group over `S` with geometrically connected structure morphism, `h : H ⟶ G` a
central monomorphism from a group of multiplicative type, `q : G ⟶ Q` an fppf quotient of `G` by
the image of `h`, `h' : H' ⟶ Q` a central homomorphism from a group of multiplicative type, and
`p : P ⟶ G` a monomorphism representing the preimage of the image of `h'`. Then `p` is central.

For points `g` of `G` and `y` of `P`, the commutator `⁅g, p(y)⁆` lies in the kernel of `q`, the
image of `h`, and depends only on the image of `y` in `Q`. Descending along the fppf covers that
lift points of `H'` to `P` gives a family of homomorphisms `H' → H` parametrized by `G`. By
rigidity it agrees with its value at `g = 1`, which is trivial.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace MultiplicativeTypePreimageCentral

open RelativeMultiplicativeType

variable {S : Scheme.{u}}

section GroupLemmas

variable {M : Type*} [Group M]

/-- The commutator with `g` is unchanged by right multiplication by an element commuting
with `g`. -/
theorem commutatorElement_mul_of_commute_right (g x c : M) (hc : Commute c g) :
    ⁅g, x * c⁆ = ⁅g, x⁆ := by
  have e : c * g⁻¹ = g⁻¹ * c := hc.inv_right.eq
  calc ⁅g, x * c⁆ = g * x * (c * g⁻¹) * c⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
    _ = g * x * (g⁻¹ * c) * c⁻¹ * x⁻¹ := by rw [e]
    _ = ⁅g, x⁆ := by rw [commutatorElement_def]; group

/-- The commutator with `g` is multiplicative when the commutators are central. -/
theorem commutatorElement_mul_of_commute (g x₁ x₂ : M) (hc : ∀ m : M, Commute ⁅g, x₂⁆ m) :
    ⁅g, x₁ * x₂⁆ = ⁅g, x₁⁆ * ⁅g, x₂⁆ :=
  RationalDensity.commutatorElement_mul_of_commute g x₁ x₂ hc

end GroupLemmas

/-- Two morphisms in `Over S` agree if they agree after precomposition with a morphism whose
underlying morphism of schemes is an epimorphism. -/
theorem over_ext_of_epi {U V Y : Over S} (f : U ⟶ V) [Epi f.left] {a b : V ⟶ Y}
    (hab : f ≫ a = f ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_epi f.left).mp
  exact congrArg (fun m => m.left) hab

section Cover

variable {G Q H' : GroupScheme S} (q : G ⟶ Q) (h' : H' ⟶ Q) {V : Over S} (z : V ⟶ H'.X)

/-- The `S`-scheme `G ×_Q V` over which the point `z ≫ h'` of `Q` lifts to `G`. -/
def coverObj : Over S :=
  Over.mk (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left ≫ V.hom)

/-- The projection `G ×_Q V ⟶ V`. -/
def coverMap : coverObj q h' z ⟶ V :=
  Over.homMk (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left)

/-- The tautological point of `G` over `G ×_Q V`. -/
def coverPt : coverObj q h' z ⟶ G.X :=
  Over.homMk (pullback.fst q.hom.hom.left (z ≫ h'.hom.hom).left) (by
    change _ = pullback.snd _ _ ≫ V.hom
    rw [← Over.w q.hom.hom, pullback.condition_assoc, Over.w (z ≫ h'.hom.hom)])

theorem coverPt_comp : coverPt q h' z ≫ q.hom.hom = coverMap q h' z ≫ z ≫ h'.hom.hom :=
  Over.OverMorphism.ext pullback.condition

end Cover

variable {G H Q H' P : GroupScheme S}

/-- The hypotheses used for the centrality of the preimage: `h` is a central monomorphism, `q`
is an fppf quotient by the image of `h`, `h'` is central and `p` represents the preimage under
`q` of the image of `h'`. -/
structure Hyp (h : H ⟶ G) (q : G ⟶ Q) (h' : H' ⟶ Q) (p : P ⟶ G) : Prop where
  mono : Mono h.hom.hom
  central : IsCentral h
  flat : Flat q.hom.hom.left
  surjective : Surjective q.hom.hom.left
  lfp : LocallyOfFinitePresentation q.hom.hom.left
  ker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range h
  central' : IsCentral h'
  range : SubgroupFunctor.range p = (SubgroupFunctor.range h').comap q

namespace Hyp

variable {h : H ⟶ G} {q : G ⟶ Q} {h' : H' ⟶ Q} {p : P ⟶ G} (hD : Hyp h q h' p)
include hD

theorem commute_comp {T : Over S} (k : T ⟶ H.X) (x : T ⟶ G.X) :
    Commute (k ≫ h.hom.hom) x := by
  have := hD.central T k T (𝟙 T) x
  rwa [Category.id_comp] at this

theorem exists_preimage {T : Over S} (y : T ⟶ P.X) :
    ∃ z : T ⟶ H'.X, z ≫ h'.hom.hom = y ≫ p.hom.hom ≫ q.hom.hom := by
  have hy : y ≫ p.hom.hom ∈ (SubgroupFunctor.range p).carrier T := ⟨y, rfl⟩
  rw [hD.range, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range] at hy
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, by rw [hz, Category.assoc]⟩

theorem exists_lift {T : Over S} (x : T ⟶ G.X) (z : T ⟶ H'.X)
    (hx : x ≫ q.hom.hom = z ≫ h'.hom.hom) : ∃ y : T ⟶ P.X, y ≫ p.hom.hom = x := by
  have hx' : x ∈ (SubgroupFunctor.range p).carrier T := by
    rw [hD.range, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
    exact ⟨z, hx.symm⟩
  rwa [SubgroupFunctor.mem_range] at hx'

theorem commutator_comp {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P.X) :
    ⁅g, y ≫ p.hom.hom⁆ ≫ q.hom.hom = 1 := by
  obtain ⟨z, hz⟩ := hD.exists_preimage y
  have hc : Commute (z ≫ h'.hom.hom) (g ≫ q.hom.hom) := by
    have := hD.central' T z T (𝟙 T) (g ≫ q.hom.hom)
    rwa [Category.id_comp] at this
  rw [hz, ← Category.assoc] at hc
  rw [commutatorElement_def, MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    GrpObj.inv_comp, ← commutatorElement_def, commutatorElement_eq_one_iff_commute]
  exact hc.symm

theorem exists_commutator {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P.X) :
    ∃ c : T ⟶ H.X, c ≫ h.hom.hom = ⁅g, y ≫ p.hom.hom⁆ := by
  have hm : ⁅g, y ≫ p.hom.hom⁆ ∈ (SubgroupFunctor.range (kernelι q)).carrier T :=
    (mem_range_kernelι_iff q _).2 (hD.commutator_comp g y)
  rwa [hD.ker, SubgroupFunctor.mem_range] at hm

/-- The commutator `⁅g, p(y)⁆` as a point of `H`. -/
def commH {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P.X) : T ⟶ H.X :=
  Classical.choose (hD.exists_commutator g y)

theorem commH_comp {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P.X) :
    hD.commH g y ≫ h.hom.hom = ⁅g, y ≫ p.hom.hom⁆ :=
  Classical.choose_spec (hD.exists_commutator g y)

theorem comp_commH {T T' : Over S} (a : T' ⟶ T) (g : T ⟶ G.X) (y : T ⟶ P.X) :
    a ≫ hD.commH g y = hD.commH (a ≫ g) (a ≫ y) := by
  have := hD.mono
  apply (cancel_mono h.hom.hom).mp
  simp only [Category.assoc, commH_comp, commutatorElement_def, MonObj.comp_mul,
    GrpObj.comp_inv]

/-- The commutator depends only on the image of `y` in `Q`. -/
theorem commH_eq {T : Over S} (g : T ⟶ G.X) {y₁ y₂ : T ⟶ P.X}
    (hy : y₁ ≫ p.hom.hom ≫ q.hom.hom = y₂ ≫ p.hom.hom ≫ q.hom.hom) :
    hD.commH g y₁ = hD.commH g y₂ := by
  have := hD.mono
  apply (cancel_mono h.hom.hom).mp
  rw [commH_comp, commH_comp]
  have hk : (y₁ ≫ p.hom.hom)⁻¹ * (y₂ ≫ p.hom.hom) ∈
      (SubgroupFunctor.range (kernelι q)).carrier T := by
    rw [mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp]
    simp only [Category.assoc, hy, inv_mul_cancel]
  rw [hD.ker, SubgroupFunctor.mem_range] at hk
  obtain ⟨k, hk⟩ := hk
  have hx : y₂ ≫ p.hom.hom = (y₁ ≫ p.hom.hom) * (k ≫ h.hom.hom) := by
    rw [hk, mul_inv_cancel_left]
  rw [hx, commutatorElement_mul_of_commute_right _ _ _ (hD.commute_comp k g)]

theorem commH_mul {T : Over S} (g : T ⟶ G.X) (y₁ y₂ : T ⟶ P.X) :
    hD.commH g (y₁ * y₂) = hD.commH g y₁ * hD.commH g y₂ := by
  have := hD.mono
  apply (cancel_mono h.hom.hom).mp
  rw [commH_comp, MonObj.mul_comp, MonObj.mul_comp, commH_comp, commH_comp]
  apply commutatorElement_mul_of_commute
  intro m
  rw [← hD.commH_comp]
  exact hD.commute_comp _ m

theorem commH_one_left {T : Over S} (y : T ⟶ P.X) : hD.commH 1 y = 1 := by
  have := hD.mono
  apply (cancel_mono h.hom.hom).mp
  rw [commH_comp, commutatorElement_one_left, MonObj.one_comp]

section Descent

variable {V : Over S} (z : V ⟶ H'.X)

/-- A lift of the tautological point of `G` over `G ×_Q V` to `P`. -/
def coverLift : coverObj q h' z ⟶ P.X :=
  Classical.choose (hD.exists_lift (coverPt q h' z) (coverMap q h' z ≫ z)
    (by rw [coverPt_comp, Category.assoc]))

theorem coverLift_comp : hD.coverLift z ≫ p.hom.hom = coverPt q h' z :=
  Classical.choose_spec (hD.exists_lift (coverPt q h' z) (coverMap q h' z ≫ z)
    (by rw [coverPt_comp, Category.assoc]))

theorem coverLift_q :
    hD.coverLift z ≫ p.hom.hom ≫ q.hom.hom = coverMap q h' z ≫ z ≫ h'.hom.hom := by
  rw [← Category.assoc, coverLift_comp, coverPt_comp]

/-- The commutator family on the cover `G ×_Q V`, as a morphism of schemes. -/
def descFun (g : V ⟶ G.X) : pullback q.hom.hom.left (z ≫ h'.hom.hom).left ⟶ H.X.left :=
  (hD.commH (coverMap q h' z ≫ g) (hD.coverLift z)).left

theorem descFun_compat (g : V ⟶ G.X) {Z : Scheme.{u}}
    (a₁ a₂ : Z ⟶ pullback q.hom.hom.left (z ≫ h'.hom.hom).left)
    (ha : a₁ ≫ pullback.snd _ _ = a₂ ≫ pullback.snd _ _) :
    a₁ ≫ hD.descFun z g = a₂ ≫ hD.descFun z g := by
  let Zo : Over S := Over.mk (a₁ ≫ (coverObj q h' z).hom)
  let b₁ : Zo ⟶ coverObj q h' z := Over.homMk a₁
  let b₂ : Zo ⟶ coverObj q h' z := Over.homMk a₂ (by
    change a₂ ≫ pullback.snd _ _ ≫ V.hom = a₁ ≫ pullback.snd _ _ ≫ V.hom
    rw [← Category.assoc, ← ha, Category.assoc])
  have hb : b₁ ≫ coverMap q h' z = b₂ ≫ coverMap q h' z := Over.OverMorphism.ext ha
  have e : b₁ ≫ hD.commH (coverMap q h' z ≫ g) (hD.coverLift z) =
      b₂ ≫ hD.commH (coverMap q h' z ≫ g) (hD.coverLift z) := by
    rw [hD.comp_commH, hD.comp_commH]
    have hg : b₁ ≫ coverMap q h' z ≫ g = b₂ ≫ coverMap q h' z ≫ g := by
      simp only [← Category.assoc, hb]
    rw [hg]
    apply hD.commH_eq
    simp only [Category.assoc, hD.coverLift_q]
    simp only [← Category.assoc, hb]
  exact congrArg (fun m => m.left) e

/-- **The descended commutator family.** For a point `z` of `H'` and a point `g` of `G` over
`V`, the point of `H` that is `⁅g, p(y)⁆` for every fppf-local lift `y` of `z` to `P`. -/
def K (V : Over S) (g : V ⟶ G.X) (z : V ⟶ H'.X) : V ⟶ H.X :=
  haveI := hD.flat
  haveI := hD.surjective
  haveI := hD.lfp
  Over.homMk (EffectiveEpi.desc (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left)
    (hD.descFun z g) (fun a₁ a₂ ha => hD.descFun_compat z g a₁ a₂ ha)) (by
      apply (cancel_epi (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left)).mp
      rw [EffectiveEpi.fac_assoc]
      exact Over.w (hD.commH (coverMap q h' z ≫ g) (hD.coverLift z)))

theorem coverMap_K (g : V ⟶ G.X) :
    coverMap q h' z ≫ hD.K V g z = hD.commH (coverMap q h' z ≫ g) (hD.coverLift z) := by
  have := hD.flat
  have := hD.surjective
  have := hD.lfp
  exact Over.OverMorphism.ext
    (EffectiveEpi.fac (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left) (hD.descFun z g)
      (fun a₁ a₂ ha => hD.descFun_compat z g a₁ a₂ ha))

theorem cover_ext {Y : Over S} {a b : V ⟶ Y}
    (hab : coverMap q h' z ≫ a = coverMap q h' z ≫ b) : a = b := by
  have := hD.flat
  have := hD.surjective
  have := hD.lfp
  have : Epi (coverMap q h' z).left :=
    inferInstanceAs (Epi (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left))
  exact over_ext_of_epi _ hab

/-- **Characterization of the descended family.** For `f : U ⟶ V` and a point `y` of `P` over
`U` lifting `f ≫ z`, `f ≫ K V g z = ⁅f ≫ g, p(y)⁆`. -/
theorem comp_K {U : Over S} (f : U ⟶ V) (g : V ⟶ G.X) (y : U ⟶ P.X)
    (hy : y ≫ p.hom.hom ≫ q.hom.hom = f ≫ z ≫ h'.hom.hom) :
    f ≫ hD.K V g z = hD.commH (f ≫ g) y := by
  have := hD.flat
  have := hD.surjective
  have := hD.lfp
  let U' : Over S := Over.mk (pullback.fst f.left (coverMap q h' z).left ≫ U.hom)
  let u₁ : U' ⟶ U := Over.homMk (pullback.fst f.left (coverMap q h' z).left)
  let u₂ : U' ⟶ coverObj q h' z := Over.homMk (pullback.snd f.left (coverMap q h' z).left) (by
    change _ = pullback.fst _ _ ≫ U.hom
    rw [← Over.w f, pullback.condition_assoc, Over.w (coverMap q h' z)])
  have hu : u₁ ≫ f = u₂ ≫ coverMap q h' z := Over.OverMorphism.ext pullback.condition
  have : Epi u₁.left := inferInstanceAs
    (Epi (pullback.fst f.left (pullback.snd q.hom.hom.left (z ≫ h'.hom.hom).left)))
  apply over_ext_of_epi u₁
  have hg : u₂ ≫ coverMap q h' z ≫ g = u₁ ≫ f ≫ g := by
    simp only [← Category.assoc, hu]
  rw [← Category.assoc, hu, Category.assoc, hD.coverMap_K, hD.comp_commH, hD.comp_commH, hg]
  apply hD.commH_eq
  simp only [Category.assoc, hD.coverLift_q, hy]
  simp only [← Category.assoc, hu]

end Descent

theorem K_naturality {V W : Over S} (f : W ⟶ V) (g : V ⟶ G.X) (z : V ⟶ H'.X) :
    hD.K W (f ≫ g) (f ≫ z) = f ≫ hD.K V g z := by
  apply hD.cover_ext (f ≫ z)
  have := hD.comp_K z (coverMap q h' (f ≫ z) ≫ f) g (hD.coverLift (f ≫ z))
    (by simpa only [Category.assoc] using hD.coverLift_q (f ≫ z))
  simp only [Category.assoc] at this
  rw [hD.coverMap_K, this]

theorem K_mul (V : Over S) (g : V ⟶ G.X) (z₁ z₂ : V ⟶ H'.X) :
    hD.K V g (z₁ * z₂) = hD.K V g z₁ * hD.K V g z₂ := by
  have := hD.flat
  have := hD.surjective
  have := hD.lfp
  let U' : Over S := Over.mk
    (pullback.fst (coverMap q h' z₁).left (coverMap q h' z₂).left ≫ (coverObj q h' z₁).hom)
  let u₁ : U' ⟶ coverObj q h' z₁ :=
    Over.homMk (pullback.fst (coverMap q h' z₁).left (coverMap q h' z₂).left)
  let u₂ : U' ⟶ coverObj q h' z₂ :=
    Over.homMk (pullback.snd (coverMap q h' z₁).left (coverMap q h' z₂).left) (by
      change _ = pullback.fst _ _ ≫ (coverObj q h' z₁).hom
      rw [← Over.w (coverMap q h' z₁), pullback.condition_assoc, Over.w (coverMap q h' z₂)])
  have hu : u₁ ≫ coverMap q h' z₁ = u₂ ≫ coverMap q h' z₂ :=
    Over.OverMorphism.ext pullback.condition
  let f : U' ⟶ V := u₁ ≫ coverMap q h' z₁
  have : Epi f.left := inferInstanceAs (Epi
    (pullback.fst (pullback.snd q.hom.hom.left (z₁ ≫ h'.hom.hom).left)
      (pullback.snd q.hom.hom.left (z₂ ≫ h'.hom.hom).left) ≫
      pullback.snd q.hom.hom.left (z₁ ≫ h'.hom.hom).left))
  have hy₁ : (u₁ ≫ hD.coverLift z₁) ≫ p.hom.hom ≫ q.hom.hom = f ≫ z₁ ≫ h'.hom.hom := by
    simp only [f, Category.assoc, hD.coverLift_q]
  have hy₂ : (u₂ ≫ hD.coverLift z₂) ≫ p.hom.hom ≫ q.hom.hom = f ≫ z₂ ≫ h'.hom.hom := by
    simp only [f, Category.assoc, hD.coverLift_q]
    simp only [← Category.assoc, hu]
  have hy : ((u₁ ≫ hD.coverLift z₁) * (u₂ ≫ hD.coverLift z₂)) ≫ p.hom.hom ≫ q.hom.hom =
      f ≫ (z₁ * z₂) ≫ h'.hom.hom := by
    rw [MonObj.mul_comp, hy₁, hy₂, MonObj.mul_comp, MonObj.comp_mul]
  apply over_ext_of_epi f
  rw [hD.comp_K _ f g _ hy, MonObj.comp_mul, hD.comp_K _ f g _ hy₁, hD.comp_K _ f g _ hy₂,
    hD.commH_mul]

theorem K_one (V : Over S) (z : V ⟶ H'.X) : hD.K V 1 z = 1 := by
  apply hD.cover_ext z
  rw [hD.coverMap_K, MonObj.comp_one, MonObj.comp_one, hD.commH_one_left]

/-- **The preimage is central.** -/
theorem isCentral [GeometricallyConnected G.X.hom] (hH : IsMultiplicativeType H)
    (hH' : IsMultiplicativeType H') : IsCentral p := by
  intro T y T' a g
  obtain ⟨z, hz⟩ := hD.exists_preimage (a ≫ y)
  have e := MultiplicativeTypeRigidity.eq_of_isMultiplicativeType (X := G.X) hH' hH hD.K
    hD.K_mul (fun f g z => hD.K_naturality f g z) g 1 z
  rw [hD.K_one] at e
  have e2 := hD.comp_K z (𝟙 T') g (a ≫ y) (by rw [Category.id_comp, hz])
  rw [Category.id_comp, Category.id_comp, e] at e2
  have e3 := congrArg (· ≫ h.hom.hom) e2
  simp only [MonObj.one_comp, hD.commH_comp] at e3
  rw [eq_comm, commutatorElement_eq_one_iff_commute] at e3
  rw [← Category.assoc]
  exact e3.symm

end Hyp

/-- **Centrality in part 2 of Conrad, Lemma 3.3.1.** Let `G` be a smooth affine group over `S`
with connected fibres, `h : H ⟶ G` a normal closed subgroup of multiplicative type, `q` an fppf
quotient of `G` by `H`, `h' : H' ⟶ Q` a central subgroup of multiplicative type and `p : P ⟶ G`
a subgroup representing the preimage of `H'`. Then `p` is central. -/
theorem isCentral_preimage (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left)
    {H : GroupScheme S} (h : H ⟶ G) (hh : IsClosedSubgroup h) (hH : IsMultiplicativeType H)
    (hn : (SubgroupFunctor.range h).IsNormal) {Q : GroupScheme S} (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q) {H' : GroupScheme S}
    (h' : H' ⟶ Q) (hH' : IsMultiplicativeType H') (hc' : IsCentral h') {P : GroupScheme S}
    (p : P ⟶ G) (hp : ((SubgroupFunctor.range h').comap q).IsRepresentedBy p) :
    IsCentral p := by
  have : GeometricallyConnected G.X.hom :=
    MultiplicativeTypeNormalCentral.geometricallyConnected_of_residueFiber G hG
  have : IsClosedImmersion h.hom.hom.left := hh
  have hm : Mono h.hom.hom := Over.mono_of_mono_left _
  have hc := MultiplicativeTypeNormalCentral.isCentral_of_isNormal_of_isClosedSubgroup G hG h hh
    hH hn
  obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
  exact Hyp.isCentral ⟨hm, hc, hflat, hsurj, hlfp, hker, hc', hp.2⟩ hH hH'

end MultiplicativeTypePreimageCentral

end Langlands.GroupScheme
