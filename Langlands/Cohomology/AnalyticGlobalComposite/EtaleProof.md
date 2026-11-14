# Berkovich's composite identification for étale G-sheaves

Author: Worker 280.

`analyticEtaleGlobalComposite` proves the unchanged published proposition
`Langlands.Cohomology.AnalyticGlobalComposite.AnalyticEtaleGlobalCompositeStatement`.
It retains all five universe parameters `w, u, v, uL, z`, all field and group
instances, the smallness of `G`, and the admissible-refinement instance of
the distinguished lift system. It quantifies over every supplied model of
the derived category of smooth representations and every `n : ℕ`.

The result is the natural additive identification

```
H^n(X(G), F) ≃+ Hom_D(R[0], RΓ(X{G}, F)[n]).
```

Here the left side is the published `etaleGSheafInvariantCohomology`, the
right side uses the published `etaleGSheafComplex`, and `R[0]` is the
published trivial smooth representation placed in degree zero. Naturality
is the exact equation of the statement, with the sheaf morphism acting by
postcomposition after shift on the right.

The proof installs the published sheafification and enough-injectives
instances for étale G-sheaves and Mathlib's standard derived-category
model for that source category, as used inside the definitions of the two
cohomological functors. It installs
`etaleGSheafSections_preservesInjectiveObjects` from the published constant
sheaf adjunction. It then applies `smoothGlobalComposite` to
`S = etaleGSheafSections ρ R`. The invariant sections are definitionally
`S ⋙ smoothInvariantsFunctor R G`, and the global complex is definitionally
`DerivedPlus.derivedComplex S`, so this application proves both the
isomorphisms and their full naturality directly. The accompanying
`SmoothGlobalProof.md` and `InvariantsHom.md` describe the resolution
comparison and its additive Hom construction.

The source is Berkovich, *Etale equivariant sheaves on p-adic analytic
spaces*, unfinished 1995–1996 manuscript, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed/PDF pp.4–5. These pages define invariant global sections and
smooth global sections and state the composite spectral sequence. Taking
the open subgroup to be `G` gives the equality of invariant sections with
the invariants of smooth sections. The derived-category identification
proved here is the published Library formulation behind that spectral
sequence; the spectral sequence itself is not constructed in this module.
The local PDF pages 4–5 were read for this comparison.

The proof uses only the statement's hypotheses. Continuity of the action,
Hausdorffness or compactness of the space, and compactness of the group
are not added. As explained in the unchanged statement's Markdown, its
conditional site model has broader formal scope than Berkovich's
Hausdorff continuous-action setup. The resolution argument is adapted
from the published `EquivariantComposite.GlobalProof`, using the smooth
invariants adjunction and the injective-preserving analytic section
functor. No target declaration or imported module is edited.
