# Finite presentations and finite affine sections

This internal supporting unit uses Mathlib's existing
`SheafOfModules.IsFinitePresentation` for the local finite-presentation
condition of Stacks Project, Situation 99.5.1 (Tag 08KA, retained original
`08KA.html`, source `stacks-coherent-sheaf-stack-08ka-2026-11-01`).
That predicate gives a cover and a finite free presentation on each
over-site. It implies quasi-coherence and finite type.

The principal consequence here is
`hasFiniteAffineSections_of_isFinitePresentation`: on every affine open,
the module of sections is finitely generated over the ring of functions.
The stronger `hasFiniteAffineSections_of_isFiniteType` requires only
quasi-coherence and Mathlib's local finite-type condition. No noetherian
or quasi-compact hypothesis is imposed on the scheme.

The proof transports the local finite generating sections from an
over-site to the actual open subscheme. The resulting epimorphism from
a finite free module has finitely generated affine sections because
epimorphisms of quasi-coherent sheaves are surjective on affine sections.
The existing local-to-global theorem for finite affine sections completes
the proof. `freeSectionsIso` identifies evaluation of the finite free
sheaf with a finite power of the section ring, using finite coproducts
and products in the module category.
