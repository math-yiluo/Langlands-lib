import Langlands.GroupScheme.Absolute.BorelProperQuotientStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Reduction of parabolic quotient properness to a Borel quotient over `k̄` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicQuotient

section Factor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A morphism constant on the cosets `g · range j` factors through a flat surjective
quasi-compact morphism whose fibers lie in those cosets. -/
theorem exists_factor (j : H ⟶ G) {Q₁ Q₂ : Over S} (q₁ : G.X ⟶ Q₁) (q₂ : G.X ⟶ Q₂)
    [Flat q₁.left] [Surjective q₁.left] [QuasiCompact q₁.left]
    (h₁ : ∀ (T : Over S) (g h : T ⟶ G.X), g ≫ q₁ = h ≫ q₁ →
      g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T)
    (h₂ : ∀ (T : Over S) (g h : T ⟶ G.X), g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T →
      g ≫ q₂ = h ≫ q₂) :
    ∃ φ : Q₁ ⟶ Q₂, q₁ ≫ φ = q₂ := by
  have key : ∀ {Z : Scheme.{u}} (a b : Z ⟶ G.X.left), a ≫ q₁.left = b ≫ q₁.left →
      a ≫ q₂.left = b ≫ q₂.left := by
    intro Z a b hab
    let T : Over S := Over.mk (a ≫ G.X.hom)
    have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
      rw [← Over.w q₁, ← Category.assoc, ← hab, Category.assoc]
    let a' : T ⟶ G.X := Over.homMk a rfl
    let b' : T ⟶ G.X := Over.homMk b hb
    have hq : a' ≫ q₁ = b' ≫ q₁ := Over.OverMorphism.ext hab
    exact congrArg CommaMorphism.left (h₂ T a' b' (h₁ T a' b' hq))
  let φl : Q₁.left ⟶ Q₂.left := EffectiveEpi.desc q₁.left q₂.left key
  have hφ : q₁.left ≫ φl = q₂.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk φl ?_, Over.OverMorphism.ext hφ⟩
  rw [← cancel_epi q₁.left, ← Category.assoc, hφ, Over.w q₂, Over.w q₁]

/-- Universal closedness passes along a morphism of relative schemes that is surjective. -/
theorem universallyClosed_of_surjective {Q₁ Q₂ : Over S} (φ : Q₁ ⟶ Q₂) [Surjective φ.left]
    [UniversallyClosed Q₁.hom] : UniversallyClosed Q₂.hom := by
  have : UniversallyClosed (φ.left ≫ Q₂.hom) := by rw [Over.w φ]; infer_instance
  exact UniversallyClosed.of_comp_surjective φ.left Q₂.hom

end Factor

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- Composition with the base change of `q` corresponds to composition with `q` under the
pullback adjunction on points. -/
theorem baseChangePointsEquiv_comp_map (G : GroupScheme S) {Q : Over S} (q : G.X ⟶ Q)
    (T : Over S') (g : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    ((Over.mapPullbackAdj b).homEquiv T Q).symm (g ≫ (Over.pullback b).map q) =
      baseChangePointsEquiv b G T g ≫ q :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

/-- The coset-constancy condition on a morphism passes to its base change. -/
theorem baseChange_coset {G P : GroupScheme S} (i : P ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
    (hq : ∀ (T : Over S) (g h : T ⟶ G.X), g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T →
      g ≫ q = h ≫ q)
    (T : Over S') (g h : T ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hgh : g⁻¹ * h ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).carrier T) :
    g ≫ (Over.pullback b).map q = h ≫ (Over.pullback b).map q := by
  apply ((Over.mapPullbackAdj b).homEquiv T Q).symm.injective
  rw [baseChangePointsEquiv_comp_map, baseChangePointsEquiv_comp_map]
  apply hq
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hgh
  refine SubgroupFunctor.mem_range.mpr ⟨baseChangePointsEquiv b P T y, ?_⟩
  rw [← baseChangePointsEquiv_comp]
  change baseChangePointsEquiv b G T (y ≫ ((GroupScheme.baseChange b).map i).hom.hom) = _
  rw [hy, map_mul, map_inv]

/-- The base change of a surjective morphism of relative schemes is surjective. -/
theorem surjective_baseChange_map {Q₁ Q₂ : Over S} (q : Q₁ ⟶ Q₂) [Surjective q.left] :
    Surjective ((Over.pullback b).map q).left :=
  MorphismProperty.overPullbackMap (P := @Surjective) b q ‹_›

end BaseChange

section Field

variable {k : Type u} [Field k]

instance : Surjective (toAlgebraicClosure k) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

instance : IsIntegralHom (toAlgebraicClosure k) := by
  rw [IsIntegralHom.SpecMap_iff]
  exact Algebra.IsIntegral.isIntegral (R := k) (A := AlgebraicClosure k)

instance : Flat (toAlgebraicClosure k) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

/-- Universal closedness descends along the base change to the algebraic closure. -/
theorem universallyClosed_of_baseChange (Q : Over (Spec (CommRingCat.of k)))
    (h : UniversallyClosed ((Over.pullback (toAlgebraicClosure k)).obj Q).hom) :
    UniversallyClosed Q.hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end Field

section Connected

variable {K L : Type u} [Field K] [Field L]

/-- The fibre of `X ×_K L → X` over a rational point of `X` is connected: it is isomorphic to
`Spec L`. -/
theorem isConnected_preimage_range_section {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ f = 𝟙 _) :
    _root_.IsConnected ((pullback.fst f g) ⁻¹' Set.range e) := by
  let p := pullback.fst f g
  let s := pullback.snd f g
  let j : Spec (CommRingCat.of L) ⟶ pullback f g :=
    pullback.lift (g ≫ e) (𝟙 _) (by simp [Category.assoc, he])
  have hjp : j ≫ p = g ≫ e := pullback.lift_fst _ _ _
  have hjs : j ≫ s = 𝟙 _ := pullback.lift_snd _ _ _
  let l : Spec (CommRingCat.of L) ⟶ pullback p e :=
    pullback.lift j g hjp
  let d : pullback p e ⟶ Spec (CommRingCat.of L) :=
    pullback.fst p e ≫ s
  have hlp : l ≫ pullback.fst p e = j := pullback.lift_fst _ _ _
  have hlq : l ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  have hdg : d ≫ g = pullback.snd p e := by
    dsimp only [d, s, p]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, he, Category.comp_id]
  have hdj : d ≫ j = pullback.fst p e := by
    apply pullback.hom_ext
    · change (d ≫ j) ≫ p = pullback.fst p e ≫ p
      rw [Category.assoc, hjp, ← Category.assoc, hdg, pullback.condition]
    · change (d ≫ j) ≫ s = pullback.fst p e ≫ s
      rw [Category.assoc, hjs, Category.comp_id]
  let iso : pullback p e ≅ Spec (CommRingCat.of L) := {
    hom := d
    inv := l
    hom_inv_id := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, hlp, Category.id_comp] using hdj
      · simpa only [Category.assoc, hlq, Category.id_comp] using hdg
    inv_hom_id := by
      dsimp only [d]
      rw [← Category.assoc, hlp, hjs] }
  have : IsIso iso.hom := iso.isIso_hom
  have : ConnectedSpace ↥(pullback p e) :=
    iso.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  have h := isConnected_range (pullback.fst p e).continuous
  rwa [Scheme.Pullback.range_fst] at h

/-- A connected scheme over a field `K` with a rational point stays connected after a
universally closed base change to a field `L`. -/
theorem connectedSpace_pullback_of_section {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of K))
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) [UniversallyClosed g]
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ f = 𝟙 _) :
    ConnectedSpace ↥(pullback f g) := by
  have hF := isConnected_preimage_range_section f g e he
  let p := pullback.fst f g
  have hp : ∀ t : Set ↥(pullback f g), IsClopen t → t.Nonempty → p '' t = Set.univ := by
    intro t ht hne
    exact (isClopen_iff.mp ⟨p.isClosedMap _ ht.1, p.isOpenMap _ ht.2⟩).resolve_left
      (hne.image p).ne_empty
  have hmem : ∀ t : Set ↥(pullback f g), IsClopen t → t.Nonempty →
      (p ⁻¹' Set.range e ∩ t).Nonempty := by
    intro t ht hne
    have h : e default ∈ p '' t := by rw [hp t ht hne]; trivial
    obtain ⟨a, hat, ha⟩ := h
    exact ⟨a, ⟨default, ha.symm⟩, hat⟩
  refine connectedSpace_iff_clopen.mpr ⟨⟨hF.nonempty.some⟩, fun s hs => ?_⟩
  by_contra h
  rw [not_or] at h
  have hsub := hF.isPreconnected.subset_isClopen hs
    (hmem s hs (Set.nonempty_iff_ne_empty.mpr h.1))
  obtain ⟨a, haF, has⟩ := hmem sᶜ hs.compl (Set.nonempty_compl.mpr h.2)
  exact has (hsub haF)

end Connected

section Inner

variable {S : Scheme.{u}} {G H P : GroupScheme S}

/-- If `i₀ ≫ Int(g) = f ≫ i`, then `Int(g) ≫ q` is constant on the cosets `x · range i₀`
whenever `q` is constant on the cosets `x · range i`. -/
theorem innerIso_coset (i₀ : H ⟶ G) (i : P ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X) (f : H ⟶ P)
    (hf : i₀ ≫ (G.innerIso g).hom = f ≫ i) {Q : Over S} (q : G.X ⟶ Q)
    (hq : ∀ (T : Over S) (x y : T ⟶ G.X), x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T →
      x ≫ q = y ≫ q)
    (T : Over S) (x y : T ⟶ G.X) (hxy : x⁻¹ * y ∈ (SubgroupFunctor.range i₀).carrier T) :
    x ≫ (G.innerIso g).hom.hom.hom ≫ q = y ≫ (G.innerIso g).hom.hom.hom ≫ q := by
  rw [← Category.assoc, ← Category.assoc]
  apply hq
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hxy
  refine SubgroupFunctor.mem_range.mpr ⟨z ≫ f.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, ← hf, Grp.comp_hom_hom, ← Category.assoc, hz,
    comp_innerIso_hom, comp_innerIso_hom, comp_innerIso_hom]
  group

end Inner

section Assembly

/-- Properness of homogeneous quotients by parabolic subgroups, assuming that over an
algebraically closed field some Borel subgroup has proper homogeneous quotients, that Borel
subgroups are conjugate, and that homogeneous quotients by smooth closed subgroups exist. -/
theorem parabolicSubgroupQuotientProper_of
    (hB : SomeBorelQuotientProperStatement.{u}) (hC : BorelConjugacyStatement.{u})
    (hE : SmoothSubgroupQuotientExistenceStatement.{u}) :
    ParabolicSubgroupQuotientProperStatement.{u} := by
  intro k _ G _ _ hconn P i hP Q q hsep hloft hqc hsm hsurj hqcq hcoset
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k)); infer_instance
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k)); infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.left :=
    connectedSpace_pullback_of_section G.X.hom (toAlgebraicClosure k)
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left (Over.w _)
  obtain ⟨B₀, i₀, hB₀, hprop⟩ := hB (AlgebraicClosure k)
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) ‹_›
  obtain ⟨Q₀, q₀, hsep₀, hloft₀, hqc₀, hsm₀, hsurj₀, hqcq₀, hcoset₀⟩ :=
    hE (AlgebraicClosure k) _ B₀ i₀ hB₀.isClosedSubgroup hB₀.smooth
  have hproper₀ : IsProper Q₀.hom :=
    hprop Q₀ q₀ hsep₀ hloft₀ hqc₀ hsm₀ hsurj₀ hqcq₀ hcoset₀
  obtain ⟨B, j, f, hj, hfj⟩ := hP.exists_isBorelSubgroup
  obtain ⟨g, φ, hg⟩ := (hC (AlgebraicClosure k) _).2 B₀ B i₀ j hB₀ hj
  have : Surjective q₀.left := hsurj₀
  have : QuasiCompact q₀.left := hqcq₀
  have : Smooth q₀.left := hsm₀
  obtain ⟨ψ, hψ⟩ := exists_factor i₀ q₀
    (_ ≫ (Over.pullback (toAlgebraicClosure k)).map q)
    (fun T x y h => (hcoset₀ T x y).mp h)
    (innerIso_coset i₀ ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) g (φ.hom ≫ f)
      (by rw [hg, ← hfj, Category.assoc]) _
      (baseChange_coset (toAlgebraicClosure k) i q (fun T x y h => (hcoset T x y).mpr h)))
  have : Surjective q.left := hsurj
  have : Surjective ((Over.pullback (toAlgebraicClosure k)).map q).left :=
    surjective_baseChange_map _ q
  have hinn : IsIso
      ((((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom.hom.hom.left) :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso
      (((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g)).isIso_hom
  have hinn' : Surjective
      ((((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom.hom.hom.left) :=
    inferInstance
  have : Surjective (q₀.left ≫ ψ.left) := by
    rw [← Over.comp_left, hψ]
    erw [Over.comp_left]
    exact ⟨(‹Surjective ((Over.pullback (toAlgebraicClosure k)).map q).left›).surj.comp
      hinn'.surj⟩
  have : Surjective ψ.left := Surjective.of_comp q₀.left ψ.left
  have : UniversallyClosed Q₀.hom := hproper₀.toUniversallyClosed
  have := universallyClosed_of_surjective ψ
  exact @IsProper.mk _ _ _ hsep (universallyClosed_of_baseChange Q this) hloft

end Assembly

end Langlands.GroupScheme.ParabolicQuotient
