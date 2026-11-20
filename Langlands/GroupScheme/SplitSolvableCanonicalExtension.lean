import Langlands.GroupScheme.Dynamic.FiberwiseContainment
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuotients
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Rational.FppfQuotientAction
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Adjoint.CenterQuotientCore

/-! # The canonical extension of a split solvable group is split -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitSolvableCanonical

open RelativeRoot

section General

variable {S : Scheme.{u}} {W H C X : GroupScheme S}

/-- The kernel of the trivial homomorphism is everything. -/
theorem range_eq_top_of_quotient_eq_zero {w : W ⟶ H} {c : H ⟶ C}
    (hc : IsFppfQuotient (SubgroupFunctor.range w) c) (h0 : c = 0) :
    SubgroupFunctor.range w = ⊤ := by
  rw [← hc.2.2.2]
  ext T x
  simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
  rw [mem_range_kernelι_iff, h0]
  exact MonObj.comp_one x

/-- An fpqc homomorphism is an epimorphism among group-scheme homomorphisms. -/
theorem eq_zero_of_comp_eq_zero (g : X ⟶ H) [QuasiCompact g.hom.hom.left]
    [Flat g.hom.hom.left] [Surjective g.hom.hom.left] (c : H ⟶ C) (h : g ≫ c = 0) :
    c = 0 := by
  have hk : kernelι g ≫ (0 : X ⟶ C) = 0 := comp_zero
  rw [FpqcHomDescent.unique g 0 hk c h, ← FpqcHomDescent.unique g 0 hk 0 comp_zero]

/-- Every subgroup functor of a group scheme with commuting points is normal. -/
theorem isNormal_of_commute (F : SubgroupFunctor H)
    (hc : ∀ (T : Over S) (g x : T ⟶ H.X), Commute g x) : F.IsNormal := by
  intro T g x _ hx
  rw [(hc T g x).eq, mul_inv_cancel_right]
  exact hx

/-- A homomorphism whose source lies in the kernel of `q` composes with `q` to zero. -/
theorem comp_eq_zero_of_range_le (w : W ⟶ H) (c : H ⟶ C)
    (h : SubgroupFunctor.range w ≤ SubgroupFunctor.range (kernelι c)) : w ≫ c = 0 := by
  apply (Grp.forget _).map_injective
  change w.hom.hom ≫ c.hom.hom = (1 : W.X ⟶ C.X)
  have hw : 𝟙 W.X ≫ w.hom.hom ∈ (SubgroupFunctor.range w).carrier W.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
  have := (mem_range_kernelι_iff c _).mp (h W.X hw)
  rwa [Category.id_comp] at this

/-- A homomorphism between quasi-compact and quasi-separated group schemes is quasi-compact. -/
theorem quasiCompact_hom (f : W ⟶ H) [QuasiCompact W.X.hom] [QuasiSeparated H.X.hom] :
    QuasiCompact f.hom.hom.left := by
  have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  exact QuasiCompact.of_comp _ H.X.hom

/-- A factor of a closed subgroup inclusion through a separated homomorphism is a closed
subgroup inclusion. -/
theorem isClosedSubgroup_of_comp (f : W ⟶ H) (g : H ⟶ C) (h : IsClosedSubgroup (f ≫ g))
    [IsSeparated g.hom.hom.left] : IsClosedSubgroup f := by
  have : IsClosedImmersion (f.hom.hom.left ≫ g.hom.hom.left) := h
  exact IsClosedImmersion.of_comp f.hom.hom.left g.hom.hom.left

/-- The kernel of `j ≫ q` for a monomorphism `j` is computed inside the image of `j`. -/
theorem range_kernelι_comp_eq {N U' : GroupScheme S} (j : N ⟶ H) [Mono j.hom.hom]
    (q : H ⟶ C) (i' : U' ⟶ N)
    (h : ∀ (T : Over S) (y : T ⟶ H.X), y ∈ (SubgroupFunctor.range j).carrier T →
      (y ∈ (SubgroupFunctor.range (kernelι q)).carrier T ↔
        y ∈ (SubgroupFunctor.range (i' ≫ j)).carrier T)) :
    SubgroupFunctor.range (kernelι (j ≫ q)) = SubgroupFunctor.range i' := by
  ext T x
  rw [mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc, ← mem_range_kernelι_iff,
    h T _ (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)]
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨u, (cancel_mono j.hom.hom).mp ?_⟩
    rw [Category.assoc]
    exact hu
  · intro hx
    obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨u, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- A monomorphism into a trivial group scheme has trivial source. -/
theorem range_id_eq_bot_of_mono (i : W ⟶ H) [Mono i.hom.hom]
    (hH : SubgroupFunctor.range (𝟙 H) = ⊥) : SubgroupFunctor.range (𝟙 W) = ⊥ := by
  have h1 := CenterQuotient.id_eq_one_of_range_id_eq_bot hH
  have h2 : 𝟙 W.X = (1 : W.X ⟶ W.X) := by
    apply (cancel_mono i.hom.hom).mp
    rw [Category.id_comp, MonObj.one_comp, ← Category.comp_id i.hom.hom, h1, MonObj.comp_one]
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change y ≫ 𝟙 W.X = 1
    rw [h2, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

/-- A group scheme with trivial point functor is the split torus of rank zero. -/
theorem isSplitTorus_of_range_id_eq_bot (h : SubgroupFunctor.range (𝟙 H) = ⊥) :
    IsSplitTorus H := by
  have h1 := CenterQuotient.id_eq_one_of_range_id_eq_bot h
  have hu : ∀ (T : Over S) (x : T ⟶ H.X), x = 1 := fun T x => by
    rw [← Category.comp_id x, h1, MonObj.comp_one]
  let _ : ∀ T : Over S, Unique (T ⟶ H.X) := fun T => ⟨⟨1⟩, fun x => hu T x⟩
  exact ⟨PEmpty, inferInstance, ⟨isoOfPointModels
    (fun T : Over S => PEmpty.{u + 1} → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict PEmpty a) (fun _ => MulEquiv.ofUnique)
    (splitTorus.pointsEquiv PEmpty) (fun _ _ => Subsingleton.elim _ _)
    (fun a y => splitTorus.pointsEquiv_naturality PEmpty a y)⟩⟩

/-- Every homomorphism out of a group scheme with trivial point functor is zero. -/
theorem eq_zero_of_range_id_eq_bot_source (hH : SubgroupFunctor.range (𝟙 H) = ⊥)
    (q : H ⟶ C) : q = 0 := by
  apply (Grp.forget _).map_injective
  change q.hom.hom = (1 : H.X ⟶ C.X)
  rw [← Category.id_comp q.hom.hom, CenterQuotient.id_eq_one_of_range_id_eq_bot hH,
    MonObj.one_comp]

/-- The trivial homomorphism has trivial range. -/
theorem range_zero_eq_bot : SubgroupFunctor.range (0 : W ⟶ H) = ⊥ := by
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact MonObj.comp_one y
  · rintro rfl
    exact Subgroup.one_mem _

end General

section Field

variable {k : Type u} [Field k]

/-- An fppf image of an affine group scheme of finite type over a field is affine and of
finite type. -/
theorem quotient_geometry {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] :
    IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcomp : LocallyOfFiniteType (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have hlft : LocallyOfFiniteType Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp
      _ _ _ q.hom.hom.left Q.X.hom inferInstance inferInstance inferInstance hcomp
  have : CompactSpace Q.X.left := Function.Surjective.compactSpace
    q.hom.hom.left.continuous q.hom.hom.left.surjective
  have : QuasiCompact Q.X.hom := inferInstance
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact ⟨affineGroupSchemeQuotient k G Q q, hlft⟩

/-- A homomorphism of affine group schemes of finite type over a field, with commutative
target, is flat, surjective and locally of finite presentation as soon as every affine fppf
quotient of the target killing its image is trivial. -/
theorem fppf_of_quotients_trivial {X Y : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.X.hom] [IsAffineHom X.X.hom]
    [LocallyOfFiniteType Y.X.hom] [IsAffineHom Y.X.hom] (f : X ⟶ Y)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (g x : T ⟶ Y.X), Commute g x)
    (h : ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : Y ⟶ C),
      IsAffineHom C.X.hom → LocallyOfFiniteType C.X.hom → Flat c.hom.hom.left →
      Surjective c.hom.hom.left → LocallyOfFinitePresentation c.hom.hom.left →
      f ≫ c = 0 → c = 0) :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      LocallyOfFinitePresentation f.hom.hom.left := by
  obtain ⟨I, π, w, _, _, hw, hπw, hπ⟩ := affineHomImage k X Y f
  obtain ⟨C, c, hC₁, hC₂, hc⟩ :=
    affineNormalSubgroupQuotient k Y I w hw (isNormal_of_commute _ hcomm)
  have hwc : w ≫ c = 0 := comp_eq_zero_of_range_le w c hc.2.2.2.ge
  have hc0 : c = 0 := h C c hC₂ hC₁ hc.1 hc.2.1 hc.2.2.1 (by
    rw [← hπw, Category.assoc, hwc, comp_zero])
  have htop := range_eq_top_of_quotient_eq_zero hc hc0
  have : IsClosedImmersion w.hom.hom.left := hw
  have : Mono w.hom.hom := Over.mono_of_mono_left _
  have : IsIso w.hom.hom := DynamicContainment.isIso_of_range_eq_top w htop
  have : IsIso w.hom.hom.left := (Over.forget _).map_isIso w.hom.hom
  have hf : f.hom.hom.left = π.hom.hom.left ≫ w.hom.hom.left := by
    rw [← hπw]
    rfl
  obtain ⟨h1, h2, h3, -⟩ := hπ
  rw [hf]
  have := h1
  have := h2
  have := h3
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The induction claim: for a group with a split series of length `n`, every canonical
extension (a unipotent closed subgroup with an fppf quotient of multiplicative type) consists
of a split unipotent group and a split torus. -/
def SplitClaim (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom], SplitSolvable.HasSeries n H →
    ∀ (U D : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ H) (q : H ⟶ D),
      IsClosedSubgroup i → IsUnipotent U → IsFppfQuotient (SubgroupFunctor.range i) q →
      IsMultiplicativeType D → IsSplitUnipotent U ∧ IsSplitTorus D

/-- The base case: the trivial group. -/
theorem splitClaim_zero : SplitClaim k 0 := by
  intro H _ _ hH U D i q hi hU hq hD
  have hH' := SplitSolvable.hasSeries_zero_iff.mp hH
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : IsSeparated D.X.hom := fieldSeparated k D
  have : QuasiCompact q.hom.hom.left := quasiCompact_hom q
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  refine ⟨⟨0, range_id_eq_bot_of_mono i hH'⟩, isSplitTorus_of_range_id_eq_bot ?_⟩
  have h0 : 𝟙 D = 0 := eq_zero_of_comp_eq_zero q (𝟙 D) (by
    rw [Category.comp_id]
    exact eq_zero_of_range_id_eq_bot_source hH' q)
  rw [h0]
  exact range_zero_eq_bot

/-- The inductive step when the top quotient of the series is a one-dimensional vector
group. -/
theorem splitClaim_succ_ga {n : ℕ} (ih : SplitClaim k n)
    {H N V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (j : N ⟶ H) (q₀ : H ⟶ V) (hj : IsClosedSubgroup j)
    (hq₀ : IsFppfQuotient (SubgroupFunctor.range j) q₀) (hV : IsVectorGroupOfDimension V 1)
    (hN : SplitSolvable.HasSeries n N)
    {U D : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ H) (q : H ⟶ D)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) (hD : IsMultiplicativeType D) :
    IsSplitUnipotent U ∧ IsSplitTorus D := by
  have : IsAffineHom N.X.hom := IsClosedSubgroup.isAffineHom hj
  have : LocallyOfFiniteType N.X.hom := IsClosedSubgroup.locallyOfFiniteType hj
  have : IsAffineHom U.X.hom := IsClosedSubgroup.isAffineHom hi
  have : LocallyOfFiniteType U.X.hom := IsClosedSubgroup.locallyOfFiniteType hi
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : LocallyOfFiniteType D.X.hom := hD.locallyOfFiniteType
  have : IsSeparated D.X.hom := fieldSeparated k D
  have : IsSeparated V.X.hom := fieldSeparated k V
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : QuasiCompact q.hom.hom.left := quasiCompact_hom q
  have : Flat q₀.hom.hom.left := hq₀.1
  have : Surjective q₀.hom.hom.left := hq₀.2.1
  have : LocallyOfFinitePresentation q₀.hom.hom.left := hq₀.2.2.1
  have : QuasiCompact q₀.hom.hom.left := quasiCompact_hom q₀
  obtain ⟨_, _⟩ := quotient_geometry q₀
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hVu : IsUnipotent V := hV.isUnipotent
  -- the composite `U → V` is an fppf cover
  obtain ⟨hψ₁, hψ₂, hψ₃⟩ := fppf_of_quotients_trivial (i ≫ q₀)
    (fun _ g x => hV.points_commute g x) (by
      intro C c _ _ _ _ _ hc
      have hCu : IsUnipotent C := hVu.of_flat_surjective c
      have hk : kernelι q ≫ (q₀ ≫ c) = 0 := comp_eq_zero_of_range_le _ _ (by
        rw [hq.2.2.2]
        exact range_le_kernelι_of_comp_eq_zero i (q₀ ≫ c) (by
          rw [← Category.assoc]
          exact hc))
      have hμ := hD.hom_eq_zero_of_isUnipotent hCu (FpqcHomDescent.hom q (q₀ ≫ c) hk)
      refine eq_zero_of_comp_eq_zero q₀ c ?_
      rw [← FpqcHomDescent.fac q (q₀ ≫ c) hk, hμ, comp_zero])
  -- its kernel `U'` and the induced map `U' → N`
  have hι : IsClosedSubgroup (kernelι (i ≫ q₀)) :=
    (inferInstance : IsClosedImmersion (kernelι (i ≫ q₀)).hom.hom.left)
  have hU'u : IsUnipotent (kernel (i ≫ q₀)) :=
    unipotentClosedSubgroup k U _ (kernelι (i ≫ q₀)) hι hU
  have hιi : IsClosedSubgroup (kernelι (i ≫ q₀) ≫ i) :=
    (inferInstance : IsClosedImmersion
      ((kernelι (i ≫ q₀)).hom.hom.left ≫ i.hom.hom.left))
  have : Mono (kernelι (i ≫ q₀) ≫ i).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hle : SubgroupFunctor.range (kernelι (i ≫ q₀) ≫ i) ≤ SubgroupFunctor.range j := by
    rw [← hq₀.2.2.2]
    refine range_le_kernelι_of_comp_eq_zero _ _ ?_
    rw [Category.assoc]
    exact comp_eq_zero_of_range_le _ _ le_rfl
  have ha : SubgroupFunctor.factorOfRangeLE hle ≫ j = kernelι (i ≫ q₀) ≫ i :=
    SubgroupFunctor.factorOfRangeLE_comp hle
  have haC : IsClosedSubgroup (SubgroupFunctor.factorOfRangeLE hle) :=
    isClosedSubgroup_of_comp _ j (by rw [ha]; exact hιi)
  -- the restriction of `q` to `N` is an fppf quotient by `U'`
  have hker : SubgroupFunctor.range (kernelι (j ≫ q)) =
      SubgroupFunctor.range (SubgroupFunctor.factorOfRangeLE hle) := by
    apply range_kernelι_comp_eq j q
    intro T y hy
    rw [hq.2.2.2, ha]
    constructor
    · intro hyi
      obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hyi
      have hu : u ∈ (SubgroupFunctor.range (kernelι (i ≫ q₀))).carrier T := by
        rw [mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc,
          ← mem_range_kernelι_iff, hq₀.2.2.2]
        exact hy
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hu
      exact SubgroupFunctor.mem_range.mpr ⟨v, by rw [Grp.comp_hom_hom, Category.assoc]⟩
    · intro hy'
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hy'
      exact SubgroupFunctor.mem_range.mpr
        ⟨v ≫ (kernelι (i ≫ q₀)).hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  have hDcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (g x : T ⟶ D.X), Commute g x := by
    have := hD.isCommMonObj
    intro T g x
    exact Commute.all g x
  obtain ⟨h₁, h₂, h₃⟩ := fppf_of_quotients_trivial (j ≫ q) hDcomm (by
      intro C c _ _ _ _ _ hc
      have hCm : IsMultiplicativeType C := hD.of_fppfHom c
      have hk : kernelι q₀ ≫ (q ≫ c) = 0 := comp_eq_zero_of_range_le _ _ (by
        rw [hq₀.2.2.2]
        exact range_le_kernelι_of_comp_eq_zero j (q ≫ c) (by
          rw [← Category.assoc]
          exact hc))
      have hlam := SubgroupFunctor.eq_zero_of_range_eq_bot
        (((unipotentMultiplicativeTriviality k).2.2 V C hVu hCm).1
          (FpqcHomDescent.hom q₀ (q ≫ c) hk))
      refine eq_zero_of_comp_eq_zero q c ?_
      rw [← FpqcHomDescent.fac q₀ (q ≫ c) hk, hlam, comp_zero])
  -- the induction hypothesis on `N`
  obtain ⟨⟨r, hr⟩, hDs⟩ := ih N hN (kernel (i ≫ q₀)) D (SubgroupFunctor.factorOfRangeLE hle)
    (j ≫ q) haC hU'u ⟨h₁, h₂, h₃, hker⟩ hD
  have : IsAffineHom (kernel (i ≫ q₀)).X.hom := IsClosedSubgroup.isAffineHom hι
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement k r _ inferInstance hr
  have hsm : Smooth (kernel (i ≫ q₀)).X.hom := smooth_of_over_iso e
    (inferInstance : Smooth (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)))
  have hcon : ConnectedSpace (kernel (i ≫ q₀)).X.left :=
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.mpr
      (inferInstance : ConnectedSpace 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of k)))
  exact ⟨⟨r + 1, kernel (i ≫ q₀), V, kernelι (i ≫ q₀), i ≫ q₀, hι, hsm, hcon,
    HopfPrimitive.isNormal_range_kernelι _, ⟨hψ₁, hψ₂, hψ₃, rfl⟩, hV, hr⟩, hDs⟩

/-- The inductive step when the top quotient of the series is the multiplicative group. -/
theorem splitClaim_succ_gm {n : ℕ} (ih : SplitClaim k n)
    {H N V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (j : N ⟶ H) (q₀ : H ⟶ V) (hj : IsClosedSubgroup j)
    (hq₀ : IsFppfQuotient (SubgroupFunctor.range j) q₀)
    (eV : V ≅ (Gm (Spec (CommRingCat.of k))).toGrp) (hN : SplitSolvable.HasSeries n N)
    {U D : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ H) (q : H ⟶ D)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) (hD : IsMultiplicativeType D) :
    IsSplitUnipotent U ∧ IsSplitTorus D := by
  have : IsAffineHom N.X.hom := IsClosedSubgroup.isAffineHom hj
  have : LocallyOfFiniteType N.X.hom := IsClosedSubgroup.locallyOfFiniteType hj
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : LocallyOfFiniteType D.X.hom := hD.locallyOfFiniteType
  have : IsSeparated D.X.hom := fieldSeparated k D
  have : IsSeparated V.X.hom := fieldSeparated k V
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : QuasiCompact q.hom.hom.left := quasiCompact_hom q
  have : Flat q₀.hom.hom.left := hq₀.1
  have : Surjective q₀.hom.hom.left := hq₀.2.1
  have : LocallyOfFinitePresentation q₀.hom.hom.left := hq₀.2.2.1
  have : QuasiCompact q₀.hom.hom.left := quasiCompact_hom q₀
  obtain ⟨_, _⟩ := quotient_geometry q₀
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hVs : IsSplitTorus V := isSplitTorus_gm.of_iso eV
  -- the unipotent group lies in `N`
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
    rw [← hq₀.2.2.2]
    exact range_le_kernelι_of_comp_eq_zero i q₀ (hU.hom_eq_zero_of_isSplitTorus hVs _)
  have hiN : SubgroupFunctor.factorOfRangeLE hle ≫ j = i :=
    SubgroupFunctor.factorOfRangeLE_comp hle
  have hiNC : IsClosedSubgroup (SubgroupFunctor.factorOfRangeLE hle) :=
    isClosedSubgroup_of_comp _ j (by rw [hiN]; exact hi)
  -- the induced map `χ : D → V`
  have hk : kernelι q ≫ q₀ = 0 := comp_eq_zero_of_range_le _ _ (by
    rw [hq.2.2.2, hq₀.2.2.2]
    exact hle)
  obtain ⟨χ, hχ⟩ : ∃ χ : D ⟶ V, q ≫ χ = q₀ := ⟨_, FpqcHomDescent.fac q q₀ hk⟩
  have hχ' : q.hom.hom ≫ χ.hom.hom = q₀.hom.hom := by
    rw [← Grp.comp_hom_hom, hχ]
  have : IsCommMonObj V.X := hVs.isCommMonObj
  obtain ⟨hχ₁, hχ₂, hχ₃⟩ := fppf_of_quotients_trivial χ (fun _ g x => Commute.all g x) (by
      intro C c _ _ _ _ _ hc
      refine eq_zero_of_comp_eq_zero q₀ c ?_
      rw [← hχ, Category.assoc, hc, comp_zero])
  -- the kernel `D'` of `χ` and the induced quotient map `q' : N → D'`
  have hι' : IsClosedSubgroup (kernelι χ) :=
    (inferInstance : IsClosedImmersion (kernelι χ).hom.hom.left)
  have hjq : (j ≫ q) ≫ χ = 0 ≫ kernelUnit V := by
    rw [Category.assoc, hχ, zero_comp]
    exact comp_eq_zero_of_range_le j q₀ hq₀.2.2.2.ge
  obtain ⟨q', hq'⟩ : ∃ q' : N ⟶ kernel χ, q' ≫ kernelι χ = j ≫ q :=
    ⟨Limits.pullback.lift (j ≫ q) 0 hjq, Limits.pullback.lift_fst _ _ _⟩
  -- the square `N → D'` over `H → D` is cartesian
  let eN := hq₀.kernelIso (z := j) ⟨inferInstance, rfl⟩
  have hjN : eN.inv ≫ j = kernelι q₀ := by
    rw [Iso.inv_comp_eq]
    exact (hq₀.kernelIso_hom_comp (z := j) ⟨inferInstance, rfl⟩).symm
  have hsq : IsPullback q'.hom.hom j.hom.hom (kernelι χ).hom.hom q.hom.hom := by
    have s : IsPullback (q'.hom.hom ≫ CartesianMonoidalCategory.toUnit (kernel χ).X)
        j.hom.hom η[V.X] (q.hom.hom ≫ χ.hom.hom) := by
      refine (kernel_isPullback q₀).flip.of_iso ((Grp.forget _).mapIso eN.symm) (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (CartesianMonoidalCategory.toUnit_unique _ _) ?_ ?_ ?_
      · change (kernelι q₀).hom.hom ≫ 𝟙 _ = eN.inv.hom.hom ≫ j.hom.hom
        rw [Category.comp_id, ← Grp.comp_hom_hom, hjN]
      · simp
      · rw [hχ']
        simp
    refine IsPullback.of_right s ?_ (kernel_isPullback χ).flip
    rw [← Grp.comp_hom_hom, hq', Grp.comp_hom_hom]
  have hsqS := hsq.map (Over.forget _)
  have hq'₁ : Flat q'.hom.hom.left := MorphismProperty.of_isPullback (P := @Flat) hsqS.flip hq.1
  have hq'₂ : Surjective q'.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hsqS.flip hq.2.1
  have hq'₃ : LocallyOfFinitePresentation q'.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsqS.flip hq.2.2.1
  have hker : SubgroupFunctor.range (kernelι q') =
      SubgroupFunctor.range (SubgroupFunctor.factorOfRangeLE hle) := by
    rw [← range_kernelι_comp_mono q' (kernelι χ), hq']
    apply range_kernelι_comp_eq j q
    intro T y _
    rw [hq.2.2.2, hiN]
  -- the induction hypothesis on `N`, then the central extension `D' → D → V`
  have hD'm : IsMultiplicativeType (kernel χ) := hD.of_isClosedSubgroup _ hι'
  obtain ⟨hUs, J, hJ, ⟨eZ⟩⟩ := ih N hN U (kernel χ) (SubgroupFunctor.factorOfRangeLE hle) q'
    hiNC hU ⟨hq'₁, hq'₂, hq'₃, hker⟩ hD'm
  obtain ⟨I, hI, ⟨eT⟩⟩ := hVs
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  refine ⟨hUs, CentralExtensionHopfSpec.isSplitTorus_of_split eZ eT (kernelι χ) hι' ?_ χ
    ⟨hχ₁, hχ₂, hχ₃, rfl⟩⟩
  have : IsCommMonObj D.X := hD.isCommMonObj
  intro T x T' a h
  exact Commute.all _ _

/-- The induction claim holds for every length. -/
theorem splitClaim (n : ℕ) : SplitClaim k n := by
  induction n with
  | zero => exact splitClaim_zero
  | succ n ih =>
    intro H _ _ hH U D i q hi hU hq hD
    obtain ⟨N, V, j, q₀, hj, -, -, -, hq₀, hV, hN⟩ :=
      (SplitSolvable.hasSeries_succ_iff n).mp hH
    rcases hV with hV | hV
    · exact splitClaim_succ_ga ih j q₀ hj hq₀ hV hN i q hi hU hq hD
    · obtain ⟨eV⟩ := hV
      exact splitClaim_succ_gm ih j q₀ hj hq₀ eV hN i q hi hU hq hD

/-- Milne 2017, Corollary 16.56, the splitting part: in the canonical extension
`e → U → G → D → e` of a split solvable group `G` over a field, the unipotent part `U` is split
unipotent and the multiplicative part `D` is a split torus. -/
theorem canonicalExtension_split {G U D : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSplitSolvableGroupScheme G) (i : U ⟶ G) (q : G ⟶ D) (hi : IsClosedSubgroup i)
    (hU : IsUnipotent U) (hq : IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsMultiplicativeType D) : IsSplitUnipotent U ∧ IsSplitTorus D := by
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨n, hn⟩ := hG.hasSeries
  exact splitClaim (k := k) n G hn U D i q hi hU hq hD

end Field

end SplitSolvableCanonical

end Langlands.GroupScheme
