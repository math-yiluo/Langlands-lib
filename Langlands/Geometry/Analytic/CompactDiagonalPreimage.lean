import Langlands.Geometry.Analytic.CompactSmallFibreProduct
import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange
import Langlands.Geometry.Analytic.LocalizedPullbackCompactPreimages

/-! # Compact preimages of a compact analytic-domain diagonal -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {U V B X P Q : LocalizedCategory.{u, v, v} (K := K)}

private theorem map_comp_apply {A B C : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ B) (g : B ⟶ C) (x : localizedSpaceFunctor.obj A) :
    localizedSpaceFunctor.map (f ≫ g) x =
      localizedSpaceFunctor.map g (localizedSpaceFunctor.map f x) := by
  rw [CategoryTheory.Functor.map_comp, TopCat.comp_app]

/-- Pulling an actual diagonal domain back to the product over `X`
produces a compact Hausdorff domain. The auxiliary product over `X`
need only have the compact-preimage property for compatible points. -/
theorem isCompactSpace_domainPreimage_diagonal
    {f : U ⟶ B} {g : V ⟶ B} {b : B ⟶ X}
    {p : P ⟶ U} {q : P ⟶ V} {s t : Q ⟶ B}
    (hP : IsPullback p q (f ≫ b) (g ≫ b)) (hQ : IsPullback s t b b)
    (hf : quasiEtale (f ≫ b)) (hb : quasiEtale b)
    (hU : IsCompactSpace U) (hV : IsCompactSpace V) (hB : IsCompactSpace B)
    {m : P ⟶ Q} (hs : m ≫ s = p ≫ f) (ht : m ≫ t = q ≫ g)
    (D : (presentationOf Q).AnalyticDomain) (e : B ≅ domainObj Q D)
    (he : hQ.lift (𝟙 B) (𝟙 B) rfl = e.hom ≫ domainι Q D) :
    IsCompactSpace (domainObj P (domainPreimage m D)) := by
  let : T2Space (localizedSpaceFunctor.obj U) := hU.2
  let : T2Space (localizedSpaceFunctor.obj V) := hV.2
  let : T2Space (localizedSpaceFunctor.obj B) := hB.2
  let : CompactSpace (localizedSpaceFunctor.obj U) := hU.1
  let : CompactSpace (localizedSpaceFunctor.obj V) := hV.1
  let C : Set (localizedSpaceFunctor.obj U × localizedSpaceFunctor.obj V) :=
    {z | localizedSpaceFunctor.map f z.1 = localizedSpaceFunctor.map g z.2}
  have hCc : IsCompact C := (isClosed_eq
    ((localizedSpaceFunctor.map f).hom.continuous.comp continuous_fst)
    ((localizedSpaceFunctor.map g).hom.continuous.comp continuous_snd)).isCompact
  have hC (z) (hz : z ∈ C) :
      localizedSpaceFunctor.map (f ≫ b) z.1 = localizedSpaceFunctor.map (g ≫ b) z.2 := by
    rw [map_comp_apply, map_comp_apply]
    exact congrArg (fun x : localizedSpaceFunctor.obj B => localizedSpaceFunctor.map b x) hz
  have hP' := hasCompactPairPreimages_of_quasiEtale hP hf
  let : T2Space (presentationOf P).presentation.space := hP'.1
  let : T2Space (presentationOf Q).presentation.space :=
    (hasCompactPairPreimages_of_quasiEtale hQ hb).1
  have hPc := hP'.2 C hCc hC
  have hDc : IsCompact D.carrier := isCompact_iff_compactSpace.mpr (hB.of_iso e).1
  let E := domainPreimage m D
  have hEclosed : IsClosed E.carrier :=
    hDc.isClosed.preimage (localizedSpaceFunctor.map m).hom.continuous
  let d := hQ.lift (𝟙 B) (𝟙 B) rfl
  have hd₁ : d ≫ s = 𝟙 B := hQ.lift_fst _ _ rfl
  have hd₂ : d ≫ t = 𝟙 B := hQ.lift_snd _ _ rfl
  have hd : e.inv ≫ d = domainι Q D := by
    change e.inv ≫ hQ.lift (𝟙 B) (𝟙 B) rfl = _
    rw [he, Iso.inv_hom_id_assoc]
  have hsub : E.carrier ⊆ localizedProjectionPair p q ⁻¹' C := by
    intro x hx
    change localizedSpaceFunctor.obj P at x
    let y : localizedSpaceFunctor.obj (domainObj Q D) := ⟨localizedSpaceFunctor.map m x, hx⟩
    let z := localizedSpaceFunctor.map e.inv y
    have hm : localizedSpaceFunctor.map d z = localizedSpaceFunctor.map m x := by
      change localizedSpaceFunctor.map d (localizedSpaceFunctor.map e.inv y) = _
      rw [← map_comp_apply, hd]
      exact domainι_apply D y
    have hp : localizedSpaceFunctor.map (p ≫ f) x = z := by
      rw [← hs, map_comp_apply, ← hm, ← map_comp_apply, hd₁, CategoryTheory.Functor.map_id]
      rfl
    have hq : localizedSpaceFunctor.map (q ≫ g) x = z := by
      rw [← ht, map_comp_apply, ← hm, ← map_comp_apply, hd₂, CategoryTheory.Functor.map_id]
      rfl
    change localizedSpaceFunctor.map f (localizedSpaceFunctor.map p x) =
      localizedSpaceFunctor.map g (localizedSpaceFunctor.map q x)
    rw [← map_comp_apply, ← map_comp_apply, hp, hq]
  exact ⟨isCompact_iff_compactSpace.mp (hPc.of_isClosed_subset hEclosed hsub),
    inferInstanceAs (T2Space E.carrier)⟩

private theorem isPullback_of_relativeDiagram
    {f : U ⟶ B} {g : V ⟶ B} {b : B ⟶ X}
    {p : P ⟶ U} {q : P ⟶ V} {s t : Q ⟶ B}
    {R : LocalizedCategory.{u, v, v} (K := K)}
    {m : P ⟶ Q} {d : B ⟶ Q} {a : R ⟶ B} {j : R ⟶ P}
    (hP : IsPullback p q (f ≫ b) (g ≫ b)) (hQ : IsPullback s t b b)
    (hs : m ≫ s = p ≫ f) (ht : m ≫ t = q ≫ g)
    (hd₁ : d ≫ s = 𝟙 B) (hd₂ : d ≫ t = 𝟙 B)
    (hR : IsPullback a j d m) : IsPullback (j ≫ p) (j ≫ q) f g := by
  have hf : (j ≫ p) ≫ f = a := by
    rw [Category.assoc, ← hs, ← Category.assoc, ← hR.w, Category.assoc, hd₁, Category.comp_id]
  have hg : (j ≫ q) ≫ g = a := by
    rw [Category.assoc, ← ht, ← Category.assoc, ← hR.w, Category.assoc, hd₂, Category.comp_id]
  refine IsPullback.mk' (hf.trans hg.symm) ?_ ?_
  · intro T l r hl hr
    apply hR.hom_ext
    · rw [← hf, ← Category.assoc l, ← Category.assoc r, hl]
    · apply hP.hom_ext
      · simpa only [Category.assoc] using hl
      · simpa only [Category.assoc] using hr
  · intro T x y hw
    have hxy : x ≫ (f ≫ b) = y ≫ (g ≫ b) := by
      rw [← Category.assoc, ← Category.assoc, hw]
    let k := hP.lift x y hxy
    have hk₁ : k ≫ p = x := hP.lift_fst x y hxy
    have hk₂ : k ≫ q = y := hP.lift_snd x y hxy
    have hk : (x ≫ f) ≫ d = k ≫ m := by
      apply hQ.hom_ext
      · rw [Category.assoc, hd₁, Category.comp_id, Category.assoc, hs, ← Category.assoc k, hk₁]
      · rw [Category.assoc, hd₂, Category.comp_id, Category.assoc, ht, ← Category.assoc k, hk₂, hw]
    refine ⟨hR.lift (x ≫ f) k hk, ?_, ?_⟩
    · rw [← Category.assoc, hR.lift_snd, hk₁]
    · rw [← Category.assoc, hR.lift_snd, hk₂]

/-- A compact relative pullback realized as an actual domain of the
pullback over the ambient base. -/
structure CompactRelativePullbackData (f : U ⟶ B) (g : V ⟶ B) (p : P ⟶ U) (q : P ⟶ V) where
  domain : (presentationOf P).AnalyticDomain
  isPullback : IsPullback (domainι P domain ≫ p) (domainι P domain ≫ q) f g
  compact : IsCompactSpace (domainObj P domain)

/-- Cut the pullback over the ambient base by the domain representing
the diagonal of the compact relative base. -/
def compactRelativePullbackOfDiagonal
    {f : U ⟶ B} {g : V ⟶ B} {b : B ⟶ X}
    {p : P ⟶ U} {q : P ⟶ V} {s t : Q ⟶ B}
    (hP : IsPullback p q (f ≫ b) (g ≫ b)) (hQ : IsPullback s t b b)
    (hf : quasiEtale (f ≫ b)) (hb : quasiEtale b)
    (hU : IsCompactSpace U) (hV : IsCompactSpace V) (hB : IsCompactSpace B)
    (hdiag : IsAnalyticDomainEmbedding (hQ.lift (𝟙 B) (𝟙 B) rfl)) :
    CompactRelativePullbackData f g p q := by
  refine Classical.choice (show Nonempty (CompactRelativePullbackData f g p q) from ?_)
  have hw : (p ≫ f) ≫ b = (q ≫ g) ≫ b := by
    simpa only [Category.assoc] using hP.w
  let m := hQ.lift (p ≫ f) (q ≫ g) hw
  let d := hQ.lift (𝟙 B) (𝟙 B) rfl
  obtain ⟨D, e, he⟩ := hdiag
  let E := domainPreimage m D
  let j := domainι P E
  let a := domainPreimageMap m D ≫ e.inv
  have hE : IsPullback a j d m := by
    apply (domainPreimage_isPullback m D).flip.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp [a]
    · simp [j, E]
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
    · simp
  have hs : m ≫ s = p ≫ f := hQ.lift_fst _ _ hw
  have ht : m ≫ t = q ≫ g := hQ.lift_snd _ _ hw
  exact ⟨E, isPullback_of_relativeDiagram hP hQ hs ht
      (hQ.lift_fst _ _ rfl) (hQ.lift_snd _ _ rfl) hE,
    isCompactSpace_domainPreimage_diagonal hP hQ hf hb hU hV hB hs ht D e he⟩

end Langlands.Analytic.SaturatedAtlasPresentation
