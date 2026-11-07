import Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionStatement
import Langlands.GroupScheme.Rational.NestedParabolicPreimage
import Langlands.Representation.Exponents.LeviParabolicPreimage
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Decompositions for the supplied nested parabolic triples -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

private theorem exists_projection_radical_comparison
    {k : Type u} [Field k]
    {P Q L U PL N NL : GroupScheme (Spec (CommRingCat.of k))}
    (a : P ⟶ Q) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L)
    (n : N ⟶ P) (nL : NL ⟶ PL)
    [Mono a.hom.hom] [IsAffineHom P.X.hom] [IsAffineHom PL.X.hom]
    [LocallyOfFiniteType PL.X.hom] [IsIso (subgroupMultiplication l r)]
    (hr : IsUnipotentRadical r) (hs : IsClosedSubgroup s)
    (hn : IsUnipotentRadical n) (hnL : IsUnipotentRadical nL)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr.isNormal)) :
    ∃ t : P ⟶ PL,
      t ≫ s = a ≫ leviRetraction l r hr.isNormal ∧
      (SubgroupFunctor.range nL).comap t = SubgroupFunctor.range n := by
  let rho := leviRetraction l r hr.isNormal
  let R := LeviPreimage.group l r hr.isNormal s
  let e : P ≅ R := leviPreimageIsoOfRange a l r s hr.isNormal hs h
  let tR : R ⟶ PL := LeviPreimage.projection l r hr.isNormal s
  let t : P ⟶ PL := e.hom ≫ tR
  let vR : U ⟶ R := LeviPreimage.radicalLift l r hr.isNormal s
  let v : U ⟶ P := vR ≫ e.inv
  let j : PL ⟶ P := LeviPreimage.leviSection l r hr.isNormal s ≫ e.inv
  have he : e.hom ≫ LeviPreimage.inclusion l r hr.isNormal s = a :=
    leviPreimageIsoOfRange_hom_comp a l r s hr.isNormal hs h
  have htsec : j ≫ t = 𝟙 PL := by
    simp only [j, t, tR, Category.assoc, Iso.inv_hom_id_assoc,
      LeviPreimage.section_projection]
  have hts : t ≫ s = a ≫ rho := by
    have hw : tR ≫ s = LeviPreimage.inclusion l r hr.isNormal s ≫ rho :=
      (pullback.condition (f := rho) (g := s)).symm
    dsimp only [t]
    rw [Category.assoc, hw, ← Category.assoc, he]
  have : Smooth U.X.hom := hr.smooth
  have : ConnectedSpace U.X.left := hr.connectedSpace
  have : Smooth rho.hom.hom.left := smooth_leviRetraction l r hr.isNormal
  have : Smooth tR.hom.hom.left := SubgroupPreimage.smooth_projection rho s
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map e.hom))
  have : Smooth t.hom.hom.left := by
    change Smooth (e.hom.hom.hom.left ≫ tR.hom.hom.left)
    infer_instance
  have : Surjective t.hom.hom.left := by
    have he' : j.hom.hom.left ≫ t.hom.hom.left = 𝟙 PL.X.left :=
      congrArg (fun f : PL ⟶ PL => f.hom.hom.left) htsec
    have : Surjective (j.hom.hom.left ≫ t.hom.hom.left) := by
      rw [he']
      infer_instance
    exact Surjective.of_comp j.hom.hom.left t.hom.hom.left
  have : Mono r.hom.hom := hr.isClosedSubgroup.mono_overHom
  have : Mono vR.hom.hom := LeviPreimage.mono_radicalLift l r hr.isNormal s
  have : Mono e.inv.hom.hom := inferInstanceAs (Mono ((Grp.forget _).map e.inv))
  have : Mono v.hom.hom := by
    change Mono (vR.hom.hom ≫ e.inv.hom.hom)
    infer_instance
  have hkernel : SubgroupFunctor.range (kernelι t) = SubgroupFunctor.range v := by
    dsimp only [t, v]
    rw [range_kernelι_comp_eq_comap,
      LeviPreimage.range_kernel_projection l r hr.isNormal s]
    exact (SubgroupFunctor.range_comp_iso vR e.symm).symm
  have ht : HasSmoothConnectedUnipotentKernel t :=
    ⟨KernelRepresentative.smooth t v hkernel,
      KernelRepresentative.connectedSpace t v hkernel,
      KernelRepresentative.isUnipotent t v hkernel hr.isUnipotent⟩
  exact ⟨t, hts, ht.radical_comap_eq hn hnL⟩

private theorem range_radical_levi_preimage
    {k : Type u} [Field k]
    {P Q L U PL N NL : GroupScheme (Spec (CommRingCat.of k))}
    (a : P ⟶ Q) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L)
    (n : N ⟶ P) (nL : NL ⟶ PL)
    [Mono a.hom.hom] [Mono s.hom.hom]
    [IsAffineHom P.X.hom] [IsAffineHom PL.X.hom]
    [LocallyOfFiniteType PL.X.hom] [IsIso (subgroupMultiplication l r)]
    (hr : IsUnipotentRadical r) (hs : IsClosedSubgroup s)
    (hn : IsUnipotentRadical n) (hnL : IsUnipotentRadical nL)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr.isNormal)) :
    SubgroupFunctor.range (n ≫ a) =
      (SubgroupFunctor.range (nL ≫ s)).comap (leviRetraction l r hr.isNormal) := by
  obtain ⟨t, hts, hrad⟩ :=
    exists_projection_radical_comparison a l r s n nL hr hs hn hnL h
  let rho := leviRetraction l r hr.isNormal
  have hts' : t.hom.hom ≫ s.hom.hom = a.hom.hom ≫ rho.hom.hom :=
    congrArg (fun f => f.hom.hom) hts
  ext T x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≫ n.hom.hom ∈ ((SubgroupFunctor.range nL).comap t).carrier T := by
      rw [hrad]
      exact ⟨y, rfl⟩
    rw [SubgroupFunctor.mem_comap] at hy
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
    refine ⟨z, ?_⟩
    change z ≫ (nL ≫ s).hom.hom = (y ≫ (n ≫ a).hom.hom) ≫ rho.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc, ← hts'] using
      congrArg (fun w => w ≫ s.hom.hom) hz
  · intro hx
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hx
    have hxA : x ∈ (SubgroupFunctor.range a).carrier T := by
      rw [h, SubgroupFunctor.mem_comap]
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨z ≫ nL.hom.hom, ?_⟩
      change (z ≫ nL.hom.hom) ≫ s.hom.hom = x ≫ rho.hom.hom
      simpa only [Grp.comp_hom_hom, Category.assoc] using hz
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxA
    have hyN : y ∈ (SubgroupFunctor.range n).carrier T := by
      rw [← hrad, SubgroupFunctor.mem_comap]
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨z, ?_⟩
      apply (cancel_mono s.hom.hom).mp
      calc
        (z ≫ nL.hom.hom) ≫ s.hom.hom = x ≫ rho.hom.hom := by
          simpa only [Grp.comp_hom_hom, Category.assoc] using hz
        _ = (y ≫ t.hom.hom) ≫ s.hom.hom := by
          rw [Category.assoc, hts', ← Category.assoc, hy]
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hyN
    refine ⟨w, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hw, hy]

private theorem range_levi_intersection_of_preimage
    {S : Scheme.{u}} {P Q L U PL G : GroupScheme S}
    (a : P ⟶ Q) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L) (q : Q ⟶ G)
    [Mono q.hom.hom] [IsIso (subgroupMultiplication l r)]
    (hr : (SubgroupFunctor.range r).IsNormal)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr)) :
    SubgroupFunctor.range (s ≫ l ≫ q) =
      SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range (a ≫ q) := by
  ext T x
  change (∃ y : T ⟶ PL.X, y ≫ (s ≫ l ≫ q).hom.hom = x) ↔
    (∃ y : T ⟶ L.X, y ≫ (l ≫ q).hom.hom = x) ∧
      ∃ z : T ⟶ P.X, z ≫ (a ≫ q).hom.hom = x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y ≫ s.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩, ?_⟩
    have hy : (y ≫ s.hom.hom) ≫ l.hom.hom ∈ (SubgroupFunctor.range a).carrier T := by
      rw [h, SubgroupFunctor.mem_comap, Category.assoc, ← Grp.comp_hom_hom,
        levi_comp_leviRetraction, Grp.id_hom_hom, Category.comp_id]
      exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
    refine ⟨z, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun w => w ≫ q.hom.hom) hz
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    have hyz : y ≫ l.hom.hom = z ≫ a.hom.hom := by
      apply (cancel_mono q.hom.hom).mp
      simpa only [Grp.comp_hom_hom, Category.assoc] using hy.trans hz.symm
    have hyA : y ≫ l.hom.hom ∈ (SubgroupFunctor.range a).carrier T := ⟨z, hyz.symm⟩
    rw [h, SubgroupFunctor.mem_comap, Category.assoc, ← Grp.comp_hom_hom,
      levi_comp_leviRetraction, Grp.id_hom_hom, Category.comp_id] at hyA
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hyA
    refine ⟨w, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc, ← hw] using hy

private theorem range_product_of_levi_preimage
    {S : Scheme.{u}} {P Q L U PL G : GroupScheme S}
    (a : P ⟶ Q) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L) (q : Q ⟶ G)
    [IsIso (subgroupMultiplication l r)]
    (hr : (SubgroupFunctor.range r).IsNormal)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr)) (T : Over S) :
    ((SubgroupFunctor.range (a ≫ q)).carrier T : Set (T ⟶ G.X)) =
      ((SubgroupFunctor.range (s ≫ l ≫ q)).carrier T : Set (T ⟶ G.X)) *
        ((SubgroupFunctor.range (r ≫ q)).carrier T : Set (T ⟶ G.X)) := by
  ext x
  change (∃ y : T ⟶ P.X, y ≫ (a ≫ q).hom.hom = x) ↔ x ∈ _
  constructor
  · rintro ⟨y, rfl⟩
    let z := y ≫ a.hom.hom
    have hz : z ∈ (SubgroupFunctor.range a).carrier T := ⟨y, rfl⟩
    rw [h, SubgroupFunctor.mem_comap, comp_leviRetraction] at hz
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hz
    apply Set.mem_mul.mpr
    refine ⟨b ≫ (s ≫ l ≫ q).hom.hom, ⟨b, rfl⟩,
      radicalComponent l r z ≫ (r ≫ q).hom.hom, ⟨radicalComponent l r z, rfl⟩, ?_⟩
    have hdec := congrArg (fun w => w ≫ q.hom.hom)
      (leviComponent_mul_radicalComponent l r z)
    simpa only [z, MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc, ← hb] using hdec
  · intro hx
    obtain ⟨b', hb', c', hc', hx⟩ := Set.mem_mul.mp hx
    obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp hb'
    obtain ⟨c, rfl⟩ := SubgroupFunctor.mem_range.mp hc'
    subst x
    let z := ((b ≫ s.hom.hom) ≫ l.hom.hom) * (c ≫ r.hom.hom)
    have hz : z ∈ (SubgroupFunctor.range a).carrier T := by
      rw [h, SubgroupFunctor.mem_comap, comp_leviRetraction]
      dsimp only [z]
      rw [leviComponent_product]
      exact ⟨b, rfl⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hz
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy]
    simp only [z, MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc]

/-- The supplied nested parabolic triples have the radical intersection and
ordered rational-point products required for transitivity. -/
theorem nestedParabolicPointDecomposition :
    NestedParabolicPointDecompositionStatement.{u} := by
  intro k _ _ _ _ _ G _ P M N Q L U PL NL p m n hp hm hn hmul
    q l uQ hq hl huQ hmulQ pL mL nL hpL hmL hnL hmulL
  dsimp only
  intro hPQ _ hPL
  have : IsIso (subgroupMultiplication m n) := hmul
  have : IsIso (subgroupMultiplication l uQ) := hmulQ
  have : IsIso (subgroupMultiplication mL nL) := hmulL
  have : IsAffineHom P.X.hom := hm.isAffineHom
  have : IsAffineHom Q.X.hom := hl.isAffineHom
  have : IsAffineHom PL.X.hom := hmL.isAffineHom
  have : Smooth P.X.hom := hp.smooth
  have : Smooth Q.X.hom := hq.smooth
  have : Smooth PL.X.hom := hpL.smooth
  have : ConnectedSpace P.X.left := hm.connectedSpace
  have : ConnectedSpace Q.X.left := hl.connectedSpace
  have : ConnectedSpace PL.X.left := hmL.connectedSpace
  have : Mono q.hom.hom := hq.isClosedSubgroup.mono_overHom
  have : Mono pL.hom.hom := hpL.isClosedSubgroup.mono_overHom
  obtain ⟨a, ha, h⟩ :=
    exists_range_eq_comap_leviRetraction_of_nested_points p q l uQ pL
      hp hq.isClosedSubgroup hl.isClosedSubgroup hpL.isClosedSubgroup huQ hPQ hPL
  have : Mono a.hom.hom :=
    (IsClosedSubgroup.of_comp hq.isClosedSubgroup (ha ▸ hp.isClosedSubgroup)).mono_overHom
  have hNR := range_radical_levi_preimage a l uQ pL n nL
    huQ.1 hpL.isClosedSubgroup hn.1 hnL.1 h
  have hi : SubgroupFunctor.range (nL ≫ pL ≫ l ≫ q) =
      SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range (n ≫ p) := by
    simpa only [Category.assoc, ha] using
      range_levi_intersection_of_preimage (n ≫ a) l uQ (nL ≫ pL) q
        huQ.1.isNormal hNR
  let T := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  have hi0 : (rationalPoints.map (nL ≫ pL ≫ l ≫ q)).range =
      (rationalPoints.map (l ≫ q)).range ⊓ (rationalPoints.map (n ≫ p)).range :=
    congrArg (fun F : SubgroupFunctor G => F.carrier T) hi
  refine ⟨hi0, ?_, ?_⟩
  · have hprod := range_product_of_levi_preimage (n ≫ a) l uQ (nL ≫ pL) q
      huQ.1.isNormal hNR T
    have hprod0 :
        ((rationalPoints.map ((n ≫ a) ≫ q)).range : Set (rationalPoints G)) =
          ((rationalPoints.map ((nL ≫ pL) ≫ l ≫ q)).range : Set (rationalPoints G)) *
            ((rationalPoints.map (uQ ≫ q)).range : Set (rationalPoints G)) := hprod
    simpa only [Category.assoc, ha, ← hi0] using hprod0
  · have hprod := range_product_of_levi_preimage a l uQ pL q huQ.1.isNormal h T
    have hprod0 :
        ((rationalPoints.map (a ≫ q)).range : Set (rationalPoints G)) =
          ((rationalPoints.map (pL ≫ l ≫ q)).range : Set (rationalPoints G)) *
            ((rationalPoints.map (uQ ≫ q)).range : Set (rationalPoints G)) := hprod
    simpa only [ha] using hprod0

end Langlands.GroupScheme
